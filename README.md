# Lean 4 formalization: last iterate of clipped SGD under heavy-tailed noise

These files accompany the paper *The Cost of an Unknown Horizon for the Last Iterate of Clipped SGD under Heavy-Tailed Noise*. They contain a Lean 4 formalization, built on Mathlib, of three results stated in the paper, together with all of their local proof dependencies: the known-horizon bound of Theorem 1, which the paper cites from Jiang, Bai, and Li (2026, Theorem 1), and Theorems 5 and 11(i). Theorem, equation, and section numbers refer to the arXiv version of the paper.

## What is formalized

| Paper | Result | Lean declaration | File |
|---|---|---|---|
| Theorem 1 | Last-iterate bound for a known horizon: Algorithm 1 satisfies (3) on an event of probability at least $1-\delta$ (see the note on $\ell$ below) | `ClippedSGD.KnownHorizonMain.known_horizon_upper` | `ClippedSGD/KnownHorizonMain.lean` |
| Theorem 5 | Time-uniform lower bound for the gradient-only rules of Definition 4 | `ClippedSGD.AnytimeLower.time_uniform_obstruction` | `ClippedSGD/AnytimeLowerMain.lean` |
| Theorem 11(i) | Momentum lower bound under polynomial forgetting, with constants shared by all dimensions | `ClippedSGD.MomentumMain.main_obstruction` | `ClippedSGD/MomentumMain.lean` |

Theorem 3 (the time-uniform upper bound) and the other results of the paper are not formalized.

## Checking the proofs

Requirements: Lean 4.19.0 (installed by `elan` from `lean-toolchain`), Git, and Python 3.9 or later. Dependencies are pinned in `lake-manifest.json` (Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`); do not run `lake update`. From this directory:

```sh
lake exe cache get    # optional: downloads compiled Mathlib for the pinned commit
python3 verify.py
```

The cache contains only Mathlib and its dependencies; `verify.py` always rebuilds the files of this formalization from source. Without the cache, Mathlib is also compiled from source, which takes much longer.

`verify.py` checks the files against `source-manifest.json` and the dependency checkouts against `lake-manifest.json`, deletes the local build directory, rebuilds all 47 local modules, and runs `Audit.lean`. It passes only if the build reports no `sorry` and the three theorems above, together with 30 intermediate declarations listed in `verification-targets.json`, depend on no axioms other than `propext`, `Classical.choice`, and `Quot.sound`. The receipt and logs are written to `verification-output/`. A fresh copy of these files passed this check on 2026-10-23.

## Reading the formal statements

Lean checks that each statement follows from the definitions. The notes below match the formal statements and the definitions they use with the paper.

### Theorem 1

- **Space.** `E` is any real Hilbert space with its Borel sigma-algebra and a second-countable topology; this includes $\mathbb R^d$.
- **Objective (Assumption 1).** `f` is convex and differentiable, `gradient f` is $L$-Lipschitz (`hlip`), `xstar` is a global minimizer (`hmin`), and $\|x_1-x^\star\|\le R$, with $L,R>0$.
- **Oracle (Assumption 2).** The observations `g` are adapted to the filtration `𝓕`. For $t<T$, conditionally on `𝓕 t`, the observation `g (t+1)` has mean `gradient f` at the actual state `run … (t+1)` (`hmean`) and central $p$th moment at most $\sigma^p$ (`hmoment`). The hypothesis `hpm` states that this central moment is integrable, which follows from Assumption 2; it ensures that Lean's convention for conditional expectations of non-integrable functions plays no role.
- **Algorithm 1.** `run` uses $\ell=\log(6/\delta)$, the threshold $\max\{4LR,\sigma(T/\ell)^{1/p}\}$ (`threshold`, `UpperParameters.lean`), base step $R/(128\lambda\ell)$, steps $\eta(T-t+1)/T$ (`step`, `LinearSchedule.lean`), and clipping `clip Λ g`, which returns $g$ if $\|g\|\le\Lambda$ and $(\Lambda/\|g\|)g$ otherwise (`Clipping.lean`). `iterate` (`UpperRun.lean`) applies the unprojected clipped updates; index $t$ is the paper's $x_t$, and index $0$ repeats $x_1$.
- **Conclusion.** With probability at least $1-\delta$, $f(x_{T+1})-f(x^\star)$ is at most the minimum of the right-hand side of (3), with $\ell=\log(6/\delta)$, and $13LR^2/20$, and $\|x_t-x^\star\|^2<13R^2/10$ for $1\le t\le T+1$ on the same event.
- **Relation to Theorem 1.** The paper states Theorem 1 and Algorithm 1 with $\ell=\log(8/\delta)$, as Jiang, Bai, and Li do. Applying the Lean theorem with confidence parameter $3\delta/4$ gives $\ell=\log(8/\delta)$, the same threshold and step sizes, and probability at least $1-3\delta/4\ge1-\delta$, which is Theorem 1.

### Theorem 5

- **Rules (Definition 4).** A `Rule S` maps the time $t$, the observed gradients up to and including the current one, and a seed in `S` to a response $c_t$ (`AnytimeLowerRule.lean`). The theorem assumes that every response is nonnegative (`Nonnegative`) and that each `R t` is measurable. The state starts at $x_1=0$ and follows $x_{t+1}=x_t-c_tg_t$ (`position`; see `position_zero` and `position_step`). The rule receives no horizon, function values, or information about the instance; $p$ and $\delta$ are fixed before the rule is chosen, so the rule may depend on them.
- **Quantifiers.** For every seed law, every rule, every $1<p\le2$, $0<\delta<1/2$, $C>0$, $m\ge0$, and $r>2(p-1)/(3p-1)$, there are instance parameters for which the properties below hold and the failure probability exceeds $\delta$.
- **Instance.** `InstanceProperties` (`AnytimeLowerInstance.lean`, with the losses defined in `HingeGeometry.lean`) states that the population and sample losses are one-dimensional, convex, and globally 1-smooth and attain their minima; that the population minimizer $y$ satisfies $|y-0|\le1$; and that each sample gradient equals the population gradient plus a two-valued noise that is driven by i.i.d. Bernoulli samples, is centered, and has $p$th absolute moment at most one. They are part of the conclusion of the theorem, so they are proved for the instance it constructs. From them, `InstanceProperties.fresh_oracle` (`AnytimeLowerFresh.lean`) derives Assumption 2 in its conditional form: integrated over any event of the history, including the seed, the noise at a query point that depends on the history has mean zero and $p$th absolute moment at most the probability of the event.
- **Failure event.** `paperFailure` (`AnytimeLowerTransfer.lean`) is the event that $f(x_{t+1})-f^\star>Ct^{-r}(\log(et))^m$ for some $t\ge1$, as in (11). Under the product of the i.i.d. sample law and the seed law, it has probability strictly greater than $\delta$, and it is proved to be measurable.

### Theorem 11(i)

- **Controllers (Section 7.2).** `R d` is a controller in dimension $d$. At time $t$ it maps the gradient transcript, including the current gradient, and a seed to a momentum coefficient $\beta_t$ (Lean field `damping`), a step size $\eta_t$ (field `gain`), and a clipping scale $c_t$. The recursion (`MomentumRun.lean`) starts from zero position and velocity and sets $v_{t+1}=\beta_tv_t+c_tg_t$ and $x_{t+1}=x_t-\eta_tv_{t+1}$, as in (18). A scale $c_t\in[0,1]$ represents every radial clipping threshold.
- **Common constants (21).** `UniformControls` fixes constants $\rho>0$, $a\in[0,1)$, $H,h\ge0$, and $t_0$ for all dimensions, histories, and seeds, and requires $0\le\beta_t<1$, $0\le c_t\le1$, $0\le\eta_t\le H(t+2)^h$, and $\beta_t\le1-\rho(t+2)^{-a}$ for $t\ge t_0$. Lean time starts at $0$, so $t+2$ corresponds to the paper's $1+t$.
- **Conclusion.** For $1<p\le2$, $C>0$, $k\ge0$, and $r>\max\{2(p-1)/(3p-1),a\}$ (the Lean statement writes $2(p-1)/(3p-1)$ as `betaExponent p`, and `betaExponent_formula` proves the identity), there are a dimension, a finite prefix $N$, and an i.i.d. instance such that, with probability greater than $\delta$, some $t\le N$ has $f(x_{t+1})-f^\star>Ct^{-r}(\log(et))^k$, as in (22). `LegalInstance` (`MomentumLegalOracle.lean`) states that the population and sample losses are convex and 1-smooth and attain their minima, that a population minimizer lies at distance one from the initial point, and that the noise is additive, centered, and has $p$th norm moment at most one. `Space d` has dimension $d+2$. The Lean statement allows every $\delta<1$ and $\rho>0$, which contains the paper's ranges $\delta\in(0,1/2)$ and $\rho\in(0,1]$.

In both lower bounds, Lean time is zero-based: `position t` is the paper's state $x_{t+1}$, and `position 0` is $x_1=0$.

## License

The files in this directory are released under the Apache License 2.0 (see `LICENSE`). Lean, Mathlib, and the other dependencies are obtained separately under their own licenses.
