import Verso
import VersoManual
import VersoBlueprint
import Genl

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Full Special Linear Galois Actions" =>

This chapter tracks §3 of the paper: conditions on a prime $`l` ensuring that the image
of the Galois representation on the $`l`-power torsion points of an elliptic curve over a
number field contains $`SL_2(ℤ_l)`. None of this chapter has been formalised yet.

:::lemma_ "sl2_structure"
(Lemma 3.1) For a prime $`l ≥ 5`: the matrices
$`\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}` and
$`\begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}` generate $`SL_2(\mathbb{F}_l)`; the
group $`SL_2(\mathbb{F}_l)` has no nontrivial abelian quotients; a subgroup of
$`GL_2(\mathbb{F}_l)` containing the first matrix and a non upper triangular matrix
contains $`SL_2(\mathbb{F}_l)`; and a closed subgroup $`J ⊆ GL_2(ℤ_l)` whose image in
$`GL_2(\mathbb{F}_l)` contains the first matrix and a non upper triangular matrix
contains $`SL_2(ℤ_l)`.
:::

:::lemma_ "local_rank_one"
(Lemma 3.2) Let $`E → \mathrm{Spec}\,\mathcal{O}_K` be a one-dimensional semi-abelian
scheme over a finite extension $`K` of $`ℚ_p` with proper generic fibre and split
multiplicative special fibre, with Tate parameter $`q_E ∈ \mathfrak{m}_K`. A
one-dimensional $`\mathbb{F}_l`-subspace $`N ⊆ M_l(E)` stabilised by $`G_K` satisfies
$`v_K(q_E) ∈ l ℤ` or $`N = \mathbb{F}_l(1)`; and the quotient $`E' = E/\boldsymbol{μ}_l`
satisfies $`\deg_∞(E') = l \cdot \deg_∞(E)`.
:::

:::definition "local_height"
(Definition 3.3) The *local height* of $`E_K` is the positive integer $`v_K(q_E)`; for
potentially multiplicative reduction it is defined in $`ℚ` after dividing by the
ramification index of a finite extension where multiplicative reduction is attained.
Uses {uses "local_rank_one"}[].
:::

:::proposition "faltings_heights_divisor_infinity"
(Proposition 3.4) On $`\mathcal{M}_{\mathrm{ell}}(\overline{ℚ})`, for every $`ε > 0`:
$`\underline{\deg}_∞ \lesssim \mathrm{ht}_∞ \lesssim 12(1 + ε) \cdot
\mathrm{ht}^{\mathrm{Falt}} \lesssim (1 + ε) \cdot \mathrm{ht}_∞`, where
$`\mathrm{ht}_∞` is the height associated to the divisor at infinity of the compactified
moduli stack $`\overline{\mathcal{M}}_{\mathrm{ell}}` and
$`\mathrm{ht}^{\mathrm{Falt}}` is the Faltings height. In particular the set of points
of $`\mathcal{M}_{\mathrm{ell}}(\overline{ℚ})^{≤d}` with bounded
$`\mathrm{ht}^{\mathrm{Falt}}` is finite. Uses {uses "height_function"}[],
{uses "bd_class"}[] and {uses "heights_basic_properties"}[].
:::

:::lemma_ "global_rank_one"
(Lemma 3.5) Let $`ε > 0`, $`l` prime, $`E_F` an elliptic curve over a totally imaginary
number field $`F` with an $`l`-cyclic subgroup scheme $`H_F ⊆ E_F`, such that $`l` is
prime to the local heights of $`E` at its primes of multiplicative reduction. Then
$`\tfrac{1}{12(1+ε)}\, l \cdot \underline{\deg}_∞(E) ≤ \mathrm{ht}^{\mathrm{Falt}}(E) +
2 \log(l) + C` for a constant $`C` independent of $`E`, $`F`, $`H_F` and $`l`. Uses
{uses "local_rank_one"}[], {uses "local_height"}[] and
{uses "faltings_heights_divisor_infinity"}[].
:::

:::lemma_ "elementary_estimate"
(Lemma 3.6) For every $`ε > 0` there is a constant $`C_0 > 0` such that for all
$`x, y ∈ ℝ` with $`y ≥ 1` and $`x ≥ C_0 y^{1+ε}`, one has $`x ≥ y \log(x)`.
:::

:::lemma_ "finite_exceptional_sets"
(Lemma 3.7) For a compactly bounded $`\mathcal{K}_V ⊆
\mathcal{M}_{\mathrm{ell}}(\overline{ℚ})` and $`ε > 0`, there are a constant $`C > 0`
and a Galois-finite subset $`\mathfrak{Exc} ⊆ \mathcal{M}_{\mathrm{ell}}(\overline{ℚ})`
such that for semi-stable elliptic curves $`E_L` and primes $`l` satisfying condition
(a) ($`l ≥ 100 d\,(\mathrm{ht}^{\mathrm{Falt}} + C d^ε)` and a prime of multiplicative
reduction exists) or (b) ($`[E_L] ∈ \mathcal{K}_V` and $`l` prime to the local heights),
$`l` exceeds all local heights, multiplicative reduction exists off
$`\mathfrak{Exc}`, and any $`l`-cyclic subgroup scheme forces $`[E_L] ∈ \mathfrak{Exc}`.
Uses {uses "compactly_bounded_subset"}[], {uses "faltings_heights_divisor_infinity"}[],
{uses "global_rank_one"}[], {uses "elementary_estimate"}[] and
{uses "local_height"}[].
:::

:::theorem "full_galois_actions"
(Theorem 3.8) For a compactly bounded $`\mathcal{K}_V ⊆
\mathcal{M}_{\mathrm{ell}}(\overline{ℚ})` and $`ε > 0` there are $`C > 0` and a
Galois-finite $`\mathfrak{Exc} ⊆ \mathcal{M}_{\mathrm{ell}}(\overline{ℚ})` such that:
for every elliptic curve $`E_L` over a number field $`L` with
$`[E_L] ∉ \mathfrak{Exc}` and every prime $`l` satisfying
(a) $`l ≥ 23040 \cdot 100 d\,(\mathrm{ht}^{\mathrm{Falt}}([E_L]) + C d^ε)` with at
least one prime of potentially multiplicative reduction, or (b) $`[E_L] ∈ \mathcal{K}_V`
with $`l` prime to $`30` and to the local heights at potentially multiplicative
primes, the image of $`\mathrm{Gal}(\overline{ℚ}/L) → GL_2(ℤ_l)` contains
$`SL_2(ℤ_l)`. Uses {uses "sl2_structure"}[], {uses "local_rank_one"}[],
{uses "local_height"}[] and {uses "finite_exceptional_sets"}[].
:::
