/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Genl.Curves.Covering
import Genl.GeneralPosition.TheoremTwoOne

/-!
# [GenEll], Theorem 2.1 (ii) ⇒ (i) for curves over number fields

The two arithmetic-geometric inputs of the proof of [GenEll], Theorem 2.1, are theorems for the
height theory `Genl.Curves.theory` of curves over number fields:

* `Genl.Curves.proofPackage : theory.ProofPackage`, from the coverings ramified over the
  divisor (`Genl.Curves.nonempty_covering`) and the noncritical Belyi maps with the compactness
  argument (`Genl.Curves.nonempty_belyiDescent`);
* `Genl.Curves.statementII_implies_statementI`: the Effective Abc inequality on compactly
  bounded subsets of the tripod implies the Effective Vojta inequality
  `ht_{ω_X(D)} ≲ (1 + ε) (log-diff_X + log-cond_D)` on `U_X(ℚ̄)^{≤d}` for every hyperbolic curve
  `(X, D)` of the class `Genl.Curves.Curve`.
-/

namespace Genl.Curves

/-- **The arithmetic-geometric inputs of [GenEll], Theorem 2.1**, for curves over number
fields. -/
noncomputable def proofPackage : theory.ProofPackage where
  covering X hX d ε' hε' := Classical.choice (nonempty_covering X hX d ε' hε')
  belyi X hX hD d ε _ hfail := Classical.choice (nonempty_belyiDescent X hX hD d ε hfail)

/-- **[GenEll], Theorem 2.1, (ii) ⇒ (i)** for curves over number fields. -/
theorem statementII_implies_statementI (hII : theory.StatementII) : theory.StatementI :=
  theory.statementII_implies_statementI proofPackage hII

end Genl.Curves
