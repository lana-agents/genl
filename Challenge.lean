/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

/-
Challenge file for `leanprover/comparator`.

The task is to prove the implication (ii) ⇒ (i) of Theorem 2.1 of

  S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. 52 (2010), 1-28,

for an abstract height formalism `T : Genl.HeightTheory` (the data needed to state the
theorem, cf. `Genl.GeneralPosition.HeightTheory`) equipped with the arithmetic-geometric
inputs `A : T.ProofPackage` to the proof printed on pp. 13-14 of the paper
(cf. `Genl.GeneralPosition.ProofPackage`):

* statement (i) is the Effective Mordell/ABC/Vojta conjecture for rational points of
  bounded degree on arbitrary hyperbolic curves over number fields;
* statement (ii) is the ABC conjecture for rational points of bounded degree of the
  tripod `ℙ¹ ∖ {0, 1, ∞}` lying in a compactly bounded subset whose support contains a
  fixed finite set of primes `Σ`.

The trusted imports are `Genl.GeneralPosition.HeightTheory` (statement data) and
`Genl.GeneralPosition.ProofPackage` (proof inputs), which in turn only rely on
`Genl.Mathlib.Order.BoundedDiscrepancy` and Mathlib.
-/
import Genl.GeneralPosition.ProofPackage

theorem theorem_2_1_ii_implies_i (T : Genl.HeightTheory) (A : T.ProofPackage)
    (hII : T.StatementII) : T.StatementI := sorry
