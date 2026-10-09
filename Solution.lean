/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

/-
Solution file for `leanprover/comparator`, proving the challenge stated in
`Challenge.lean`: the implication (ii) ⇒ (i) of Theorem 2.1 of

  S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. 52 (2010), 1-28.

The proof is `Genl.HeightTheory.statementII_implies_statementI`, which follows the
argument printed on pp. 13-14 of the paper; see `Genl.GeneralPosition.TheoremTwoOne`.
-/
import Genl.GeneralPosition.TheoremTwoOne

theorem theorem_2_1_ii_implies_i (T : Genl.HeightTheory) (A : T.ProofPackage)
    (hII : T.StatementII) : T.StatementI :=
  T.statementII_implies_statementI A hII
