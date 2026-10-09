# genl — Arithmetic Elliptic Curves in General Position

A Lean 4 formalisation project for

> S. Mochizuki, *Arithmetic elliptic curves in general position*,
> Math. J. Okayama Univ. **52** (2010), 1–28.
> ([pdf](https://www.math.okayama-u.ac.jp/mjou/mjou52/_01_mochizuki.pdf), local copy in
> `paper/`)

The primary target is **Theorem 2.1** of the paper: the equivalence between

* **(i)** the Effective Mordell/ABC/Vojta conjecture for rational points of bounded
  degree on arbitrary hyperbolic curves over number fields, and
* **(ii)** the ABC conjecture for rational points of bounded degree of the tripod
  `ℙ¹ ∖ {0, 1, ∞}` lying in a compactly bounded subset whose support contains a fixed
  finite set of primes `Σ`.

The substantial implication **(ii) ⇒ (i)** is formalised, sorry-free, relative to an
abstract *height formalism* (`Genl.HeightTheory`, the data needed to state the theorem)
together with a package of arithmetic-geometric inputs (`Genl.HeightTheory.ProofPackage`,
the outputs of §1 of the paper and of the theory of noncritical Belyi maps that the
printed proof consumes). The formal proof follows the argument on pp. 13–14 of the paper
step by step; instantiating the height formalism and the proof package is tracked in the
blueprint.

---

## lana-agents fork

*This section describes the fork [lana-agents/genl](https://github.com/lana-agents/genl)
(branch `master`); everything outside it is the upstream README of
[LANA-Project/genl](https://github.com/LANA-Project/genl).*

The fork instantiates the abstract height formalism and its proof package with the genuine
height theory of curves over number fields, so that Theorem 2.1 (ii) ⇒ (i) becomes a theorem
about actual Weil heights, log-differents and log-conductors. It is a dependency of the
IUT/ABC programme [lana-agents/iut](https://github.com/lana-agents/iut), which pins
`ea2846c`.

### What the fork adds

* **A correction to the interface** (`Genl/GeneralPosition/ProofPackage.lean`). The field
  `BelyiDescent.htE_equiv : ht_E ≈ (deg E / deg ω_X) • ht_{ω_X}`, read off the chain on p. 14
  of the paper, is false for genuine Weil heights (the difference is the height of a degree
  zero class of `Pic(X) ⊗ ℚ`, unbounded in both directions unless the class is torsion). It is
  replaced by `BelyiDescent.htE_le : ht_E ≲ q • ht_{ω_X}` for a real `q > deg E / deg ω_X`,
  which is all the proof uses; `TheoremTwoOne.lean` changes only in that one step.
* **`Genl.Curves.theory : HeightTheory`** (`Genl/Curves/Theory.lean`). Curves are function
  fields inside `AlgebraicClosure (RatFunc ℚ)` (`Genl.Curves.Curve`), with a reduced divisor `D`
  that is either empty or the set of cusps of a Belyi function (this class contains the tripod
  `Genl.Curves.tripod` and all proper curves). Points are `ℚ̄`-points off `D`; `ht_{ω_X(D)}` is
  the Weil height of `K_X + D`; log-different and log-conductor come from
  [lana-agents/heights](https://github.com/lana-agents/heights); compactly bounded subsets of the
  tripod are given by `Genl.Curves.CBSData`.
* **The proof package for this theory**: `Genl.Curves.proofPackage : theory.ProofPackage`,
  built from
  * `Genl.Curves.nonempty_covering` (`Genl/Curves/Covering.lean`): the identity if `D = ∅`,
    otherwise a Kummer–Fermat covering `u^N = φ`, `v^N = 1 − φ`, via Riemann–Hurwitz and the
    Kummer discriminant bound;
  * `Genl.Curves.nonempty_belyiDescent` (`Genl/Curves/BelyiDescent.lean`): noncritical Belyi
    maps (from [lana-agents/belyi](https://github.com/lana-agents/belyi)), the compactness
    argument at `2` and `∞`, the Belyi relation for heights, the log-diff + log-cond tower
    inequality, and Proposition 1.6 for the cusp divisor.
* **`Genl.Curves.statementII_implies_statementI`** (`Genl/Curves/ProofPackage.lean`):
  Theorem 2.1 (ii) ⇒ (i) for `Genl.Curves.theory`, with no hypothesis besides statement (ii).
* `Plans/HeightTheoryPlan.md`: design, lemma DAG and progress log of this work.
* `lakefile.toml` requires `heights` by git (`lana-agents/heights` at `721496c`), which in turn
  brings `lana-agents/belyi`.

### Status

* `Genl.Curves.statementII_implies_statementI` and
  `Genl.HeightTheory.statementII_implies_statementI` are proved: there is no `sorry` in
  `Genl/` (the only one is the intended statement in `Challenge.lean`), none in the pinned
  `heights` (`721496c`, apart from its own `Comparator/Challenge.lean`) or `belyi`
  (`9ce4d3f`), and `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
* Open, and not needed by iut: curves `(X, D)` with an arbitrary reduced divisor `D` (not the
  cusps of a Belyi function); this needs coverings with prescribed ramification over arbitrary
  `D` (node F1 of the plan).

### Use in iut

`Iut.Tripod.statementI_of_statementII` (`Iut/Tripod/GeneralPosition.lean`) compares iut's
tripod with `Genl.Curves.tripod`, transports statement (ii) to `Genl.Curves.theory`, applies
`Genl.Curves.statementII_implies_statementI` and transports statement (i) back. The main
theorem `Iut.classicalABC_of_variant` uses it.

---

## Layout

* `Genl/Mathlib/` — basic ingredients intended for eventual upstreaming into Mathlib:
  * `Order/BoundedDiscrepancy.lean` — BD-classes of real valued functions
    (Definition 1.2 (ii) of the paper): the relations `f ≲[s] g` and `f ≈[s] g` and
    their calculus;
  * `NumberTheory/ArithmeticDivisor.lean` — arithmetic divisors on a number field and
    the degree homomorphism, built on `NumberField.FinitePlace`/`InfinitePlace`.
* `Genl/GeneralPosition/` — the paper-specific development:
  * `HeightTheory.lean` — the abstract height formalism and the formal statements (i)
    and (ii) of Theorem 2.1;
  * `ProofPackage.lean` — the arithmetic-geometric inputs to the proof
    (ramified coverings; noncritical Belyi maps plus compactness);
  * `TheoremTwoOne.lean` — the proofs of (ii) ⇒ (i), (i) ⇒ (ii) and the equivalence.
* `blueprint/` — a [verso-blueprint](https://github.com/leanprover/verso-blueprint)
  project covering the entire paper (§1–§4), with dependency graph and progress
  tracking. Build with `cd blueprint && lake exe vbp build`; the site is written to
  `blueprint/_out/site/html-multi/`.
* `Challenge.lean`, `Solution.lean`, `config.json` — a challenge/solution pair for
  [leanprover/comparator](https://github.com/leanprover/comparator). The challenge is
  the implication (ii) ⇒ (i) of Theorem 2.1 (`theorem_2_1_ii_implies_i`); the solution
  proves it via `Genl.HeightTheory.statementII_implies_statementI`, using no axioms
  beyond `propext`, `Quot.sound` and `Classical.choice`.
* `paper/mochizuki-mjou52.pdf` — the paper.

## Building

```bash
lake exe cache get   # fetch Mathlib olean cache
lake build           # builds the Genl library
lake build Challenge Solution
```

To verify the comparator pair (requires `landrun` and `lean4export` in `PATH`, see the
comparator README):

```bash
lake env path/to/comparator/binary config.json
```

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
