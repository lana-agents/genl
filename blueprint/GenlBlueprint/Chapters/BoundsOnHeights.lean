import Verso
import VersoManual
import VersoBlueprint
import Genl

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Bounds on Heights" =>

This chapter tracks §2 of the paper, whose only result is Theorem 2.1: the equivalence
of the Effective Mordell/ABC/Vojta conjecture for arbitrary hyperbolic curves over number
fields with the ABC conjecture for compactly bounded subsets of the tripod
$`ℙ^1_ℚ \setminus \{0, 1, ∞\}`. The implication (ii) ⇒ (i) is formalised in
`Genl/GeneralPosition/` relative to an abstract height formalism
(`Genl.HeightTheory`) together with a package of arithmetic-geometric inputs
(`Genl.HeightTheory.ProofPackage`); instantiating the package for the height theory of
§1 is tracked by the nodes `exists_ramified_covering` and `belyi_descent` below.

:::definition "height_theory" (lean := "Genl.HeightTheory")
The abstract *height formalism*: a type of "curves" $`(X, D)` over number fields with
their sets of algebraic points filtered by bounded degree, height, log-different and
log-conductor functions, hyperbolicity, the tripod, and the compactly bounded subsets of
the tripod supported at $`Σ`. This is the data needed to state Theorem 2.1, abstracted
from {uses "height_function"}[], {uses "log_diff"}[], {uses "log_cond"}[],
{uses "points_of_bounded_degree"}[] and {uses "compactly_bounded_subset"}[].
:::

:::definition "statement_i" (lean := "Genl.HeightTheory.StatementI")
(Theorem 2.1 (i)) The *Effective Mordell/ABC/Vojta conjecture*: for every hyperbolic
curve $`U_X = X \setminus D` over a number field, positive integer $`d` and $`ε > 0`,
$`\mathrm{ht}_{ω_X(D)} \lesssim (1 + ε)(\text{log-diff}_X + \text{log-cond}_D)` on
$`U_X(\overline{ℚ})^{≤d}`. Formulated inside {uses "height_theory"}[] via
{uses "bd_class"}[].
:::

:::definition "statement_ii" (lean := "Genl.HeightTheory.StatementII")
(Theorem 2.1 (ii)) The *ABC conjecture for $`Σ`-supported compactly bounded subsets*:
for every compactly bounded subset $`\mathcal{K}_V ⊆ U_ℙ(\overline{ℚ})` of the tripod
whose support contains $`Σ`, positive integer $`d` and $`ε > 0`,
$`\mathrm{ht}_{ω_ℙ(C)} \lesssim (1 + ε)(\text{log-diff}_ℙ + \text{log-cond}_C)` on
$`\mathcal{K}_V ∩ U_ℙ(\overline{ℚ})^{≤d}`. Formulated inside {uses "height_theory"}[]
via {uses "bd_class"}[].
:::

:::theorem "noncritical_belyi"
(Theorem 2.5 of *Noncritical Belyi maps*, Math. J. Okayama Univ. *46* (2004)) For a
smooth proper curve $`X` over a number field and finite sets of points
$`Ξ ⊆ X(\overline{ℚ})`, there exists a Belyi map $`φ : X → ℙ^1` which is unramified over
$`ℙ^1 \setminus \{0, 1, ∞\}` and *noncritical* at the points of $`Ξ`.
:::

:::lemma_ "exists_ramified_covering" (lean := "Genl.HeightTheory.Covering")
(First paragraph of the proof of Theorem 2.1) For every hyperbolic $`(X, D)`, degree
bound $`d` and $`ε' > 0` there is a connected finite étale Galois covering of
$`U_X`, whose normalisation $`Y → X` is a hyperbolic curve ramified at each point of
$`E = (D ×_X Y)_{\mathrm{red}}` with the same sufficiently large ramification index
$`e`, such that points of degree $`≤ d` lift to points of degree $`≤ d' = d \cdot
\deg(Y/X)`, $`\text{log-diff}_Y \lesssim \text{log-diff}_X + \text{log-cond}_D` and
$`\mathrm{ht}_{ω_X(D)} ∘ π \lesssim (1 + ε') \, \mathrm{ht}_{ω_Y}` on
$`U_Y(\overline{ℚ})^{≤d'}`. Uses {uses "heights_basic_properties"}[] and
{uses "conductors_and_log_differents"}[]; the covering exists by the well-known
structure of étale fundamental groups of hyperbolic curves in characteristic zero.
:::

:::lemma_ "belyi_descent" (lean := "Genl.HeightTheory.BelyiDescent")
(Second half of the proof of Theorem 2.1) Let $`X` be hyperbolic with $`D = ∅` and
suppose $`\mathrm{ht}_{ω_X} \lesssim (1 + ε)\,\text{log-diff}_X` *fails* on
$`X(\overline{ℚ})^{=d}`. Then there are a subset $`Ξ ⊆ X(\overline{ℚ})^{=d}` on which
the failure is unbounded, a {uses "noncritical_belyi"}[noncritical Belyi map]
$`φ : X → ℙ` mapping $`Ξ` into $`\mathcal{K}_V ∩ U_ℙ(\overline{ℚ})^{≤d'}` for a
compactly bounded subset $`\mathcal{K}_V` supported on $`V ⊇ Σ`, and, with
$`E = φ^{-1}(C)_{\mathrm{red}}`, the comparisons
$`\mathrm{ht}_{ω_X} \approx \mathrm{ht}_{ω_ℙ(C)} ∘ φ - \mathrm{ht}_E`,
$`\text{log-diff}_ℙ ∘ φ + \text{log-cond}_C ∘ φ \lesssim \text{log-diff}_X +
\text{log-cond}_E`, $`\text{log-cond}_E \lesssim \mathrm{ht}_E` and
$`\mathrm{ht}_E \approx (\deg E / \deg ω_X)\,\mathrm{ht}_{ω_X}` on $`Ξ`. Uses
{uses "compactly_bounded_subset"}[], {uses "heights_basic_properties"}[],
{uses "conductor_bounded_by_height"}[] and {uses "conductors_and_log_differents"}[];
the set $`Ξ` is produced by a compactness argument in the local points at the places of
$`V`.
:::

:::theorem "thm_2_1_ii_implies_i" (lean := "Genl.HeightTheory.statementII_implies_statementI")
(Theorem 2.1, (ii) ⇒ (i)) In every height formalism admitting the inputs
{uses "exists_ramified_covering"}[] and {uses "belyi_descent"}[],
{uses "statement_ii"}[statement (ii)] implies {uses "statement_i"}[statement (i)].
:::

:::proof "thm_2_1_ii_implies_i"
One first reduces to the case $`D = ∅`: choosing a covering as in
`exists_ramified_covering` for the tolerance $`ε' = \sqrt{1 + ε} - 1` and applying the
divisor free case to $`Y`, the comparisons along $`π` yield statement (i) for
$`(X, D)` since $`(1 + ε')^2 = 1 + ε`. The divisor free case on $`X(\overline{ℚ})^{=d}`
is proved by contradiction: if the inequality fails, `belyi_descent` produces $`Ξ`,
$`φ` and $`\mathcal{K}_V`; applying statement (ii) to $`\mathcal{K}_V` with the
tolerance $`ε' = ε / (1 + q(1 + ε))`, $`q = \deg E / \deg ω_X`, which satisfies
$`1 + ε' = (1 + ε)(1 - ε' q)`, the displayed chain of BD-inequalities on p. 14 of the
paper bounds $`\mathrm{ht}_{ω_X}` on $`Ξ` by
$`(1 + ε)\,\text{log-diff}_X` up to a constant, contradicting the unboundedness of the
failure on $`Ξ`.
:::

:::theorem "thm_2_1" (lean := "Genl.HeightTheory.statementI_iff_statementII")
(Theorem 2.1) Statements (i) and (ii) are equivalent:
{uses "statement_i"}[] holds if and only if {uses "statement_ii"}[] holds.
:::

:::proof "thm_2_1"
The implication (i) ⇒ (ii) is immediate from the definitions, since
$`\mathcal{K}_V ∩ U_ℙ(\overline{ℚ})^{≤d} ⊆ U_ℙ(\overline{ℚ})^{≤d}` and the tripod is a
hyperbolic curve; the converse is {uses "thm_2_1_ii_implies_i"}[].
:::
