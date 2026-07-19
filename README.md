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
