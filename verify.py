#!/usr/bin/env python3
"""Rebuild every local proof module and audit the selected terminal declarations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
CONFIG = json.loads((ROOT / "verification-targets.json").read_text())
TARGETS = CONFIG["audit_targets"]
TERMINALS = CONFIG["terminal_targets"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1048576), b""):
            h.update(block)
    return h.hexdigest()

def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError("Command failed: " + " ".join(args) + "\n" + p.stdout)
    return p.stdout

def verify_sources():
    expected = json.loads((ROOT / "source-manifest.json").read_text())["files"]
    for name in expected:
        p = ROOT / name
        if Path(name).is_absolute() or ".." in Path(name).parts or p.is_symlink():
            raise RuntimeError("Unsafe source manifest path: " + name)
    actual = {name: digest(ROOT / name) for name in expected}
    included = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file()
                and not any(x in {".lake", ".git", "__pycache__", "verification-output"}
                            or x.startswith(".")
                            for x in p.relative_to(ROOT).parts)
                and p.name != "source-manifest.json"}
    if included != set(expected):
        raise RuntimeError("Manifest file-set mismatch: " + repr(included.symmetric_difference(expected)))
    if actual != expected:
        raise RuntimeError("Packaged source integrity check failed")
    return actual

def dependencies():
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    result = []
    for spec in lock["packages"]:
        repo = ROOT / lock["packagesDir"] / spec["name"]
        if repo.is_symlink():
            raise RuntimeError("Dependency checkout must be a real directory: " + spec["name"])
        head = run(["git", "rev-parse", "HEAD"], repo).strip()
        dirty = run(["git", "status", "--porcelain", "--untracked-files=no"], repo)
        untracked = run(["git", "ls-files", "--others", "--exclude-standard"], repo).splitlines()
        if any(name.endswith(".lean") for name in untracked):
            raise RuntimeError("Untracked dependency Lean source: " + spec["name"])
        if head != spec["rev"] or dirty:
            raise RuntimeError("Dependency differs from lock: " + spec["name"])
        result.append({"name": spec["name"], "revision": head, "tracked_clean": True})
    return result

def cache_fingerprint():
    # Fingerprints of the reused dependency binaries (compiled Mathlib and its dependencies).
    records = {}
    for p in sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean/**/*.olean")):
        records[p.relative_to(ROOT / ".lake/packages").as_posix()] = digest(p)
    payload = json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    return {"olean_count": len(records), "sha256_of_path_hash_map": hashlib.sha256(payload).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="verification-output", help="receipt/log output directory")
    args = parser.parse_args()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    receipt = {"schema_version": 1, "mechanical_status": "FAIL",
               "targets": TARGETS, "terminal_targets": TERMINALS, "allowed_axioms": sorted(ALLOWED),
               "semantic_status": "This script checks mechanics only; README.md lists the statements and definitions to compare with the paper."}
    started = time.monotonic()
    try:
        before = verify_sources()
        receipt["source_files"] = before
        receipt["source_manifest_sha256"] = digest(ROOT / "source-manifest.json")
        # Lake resolves missing packages from the included lock; never lake update.
        version = run(["lake", "env", "lean", "--version"]).strip()
        if "version 4.19.0," not in version:
            raise RuntimeError("Expected Lean 4.19.0: " + version)
        receipt["lean_version"] = version
        receipt["dependencies_before"] = dependencies()
        receipt["dependency_cache_before"] = cache_fingerprint()
        build_dir = ROOT / ".lake/build"
        if build_dir.is_symlink():
            raise RuntimeError("Local build directory must not be a symlink")
        if build_dir.exists():
            shutil.rmtree(build_dir)
        receipt["local_build_directory_absent_before_build"] = not build_dir.exists()
        if any(ROOT.glob("ClippedSGD/**/*.olean")) or (ROOT / "ClippedSGD.olean").exists():
            raise RuntimeError("Unexpected in-source compiled local module")
        modules = json.loads((ROOT / "provenance.json").read_text())["local_modules"]
        cmd = ["lake", "build"] + CONFIG["build_modules"]
        print(f"Rebuilding all {len(modules)} local modules from source...", flush=True)
        build_log = run(cmd)
        (output / "build.log").write_text(build_log)
        if re.search(r"\bdeclaration uses ['\"]sorry['\"]", build_log):
            raise RuntimeError("Build contains a sorry warning")
        built = {}
        for module in modules:
            p = build_dir / "lib/lean" / (module.replace(".", "/") + ".olean")
            if not p.is_file():
                raise RuntimeError("Local module was not rebuilt: " + module)
            built[module] = digest(p)
        receipt["local_modules_rebuilt"] = built
        receipt["build_command"] = cmd
        audit = run(["lake", "env", "lean", "Audit.lean"])
        (output / "audit.log").write_text(audit)
        results = {}
        for target in TARGETS:
            match = re.search(r"'" + re.escape(target) + r"' depends on axioms: \[([^\]]*)\]", audit)
            if not match:
                raise RuntimeError("Missing declaration/recursive axiom output: " + target)
            axioms = {x.strip() for x in match.group(1).split(",") if x.strip()}
            if not axioms <= ALLOWED:
                raise RuntimeError("Unapproved axiom dependencies: " + repr(axioms - ALLOWED))
            # #check output starts with the constant's full name.
            if not re.search(r"(?m)^" + re.escape(target) + r"(?:\s|\.)", audit):
                raise RuntimeError("Missing #check output: " + target)
            results[target] = {"check": "PASS", "recursive_axioms": sorted(axioms), "status": "PASS"}
        receipt["declaration_results"] = results
        receipt["audit_command"] = ["lake", "env", "lean", "Audit.lean"]
        receipt["dependencies_after"] = dependencies()
        receipt["dependency_cache_after"] = cache_fingerprint()
        receipt["dependency_cache_changed"] = (receipt["dependency_cache_after"] != receipt["dependency_cache_before"])
        if verify_sources() != before:
            raise RuntimeError("Source inputs changed during verification")
        receipt["changed_inputs"] = []
        receipt["mechanical_status"] = "PASS"
        receipt["build_log_sha256"] = digest(output / "build.log")
        receipt["audit_log_sha256"] = digest(output / "audit.log")
        print(f"PASS: {len(TERMINALS)} terminal declarations and {len(TARGETS)} recursive audits; standard axioms only.", flush=True)
    except Exception as e:
        receipt["error"] = str(e)
        print(str(e), file=sys.stderr)
    finally:
        receipt["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return 0 if receipt["mechanical_status"] == "PASS" else 1

if __name__ == "__main__":
    sys.exit(main())
