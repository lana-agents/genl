import Verso
import VersoManual
import VersoBlueprint
import Genl

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Primes of Prescribed Size" =>

This chapter tracks §4 of the paper: the full Galois action result of §3 is combined
with the prime number theorem to produce bounded primes $`l` avoiding the various
characteristic primes of the elliptic curve under consideration. None of this chapter has
been formalised yet; Lemma 4.1 rests on the prime number theorem, for which Mathlib's
`PrimeNumberTheoremAnd`-style asymptotics for the Chebyshev function are the natural
entry point.

:::lemma_ "primes_of_prescribed_size"
(Lemma 4.1) Write $`θ(x) = \sum_{p < x} \log p` for the Chebyshev function and
$`x_{\mathcal{A}} = \sum_{p ∈ \mathcal{A}} \log p` for finite sets of primes
$`\mathcal{A}`. Let $`M` be a positive integer and $`ε, x_ε, C_ε > 0` with
$`0 < ε < 1/4`, $`ε x_ε > C_ε`, satisfying the stated Chebyshev bounds. Then for every
$`h ≥ 0` and every finite set of primes $`\mathcal{A}` with $`x_{\mathcal{A}} > x_ε`
there exist $`M` distinct primes $`p_1, …, p_M ∉ \mathcal{A}` with
$`h ≤ p_j ≤ (1 + 6ε) x_{\mathcal{A}} + 8h`.
:::

:::lemma_ "elementary_estimates"
(Lemma 4.2) For primes $`p_1, …, p_n` and positive integers $`h_1, …, h_n` with
$`h = \sum_j h_j \log p_j`: $`\sum_j \log p_j ≤ h` and
$`\sum_j \log h_j ≤ \sum_j \log(h_j + 1) ≤ 3h/2`.
:::

:::corollary "full_galois_degenerating"
(Corollary 4.3) For every $`ε > 0` there are $`C > 0` and a Galois-finite
$`\mathfrak{Exc} ⊆ \mathcal{M}_{\mathrm{ell}}(\overline{ℚ})` such that every elliptic
curve $`E_L` over a number field $`L` (a minimal field of definition) with
$`[E_L] ∉ \mathfrak{Exc}` and at least one prime of potentially multiplicative
reduction, and every finite set of primes $`\mathcal{S}`, admit primes
$`l_◦, l_• ∉ \mathcal{S}` prime to the primes of potentially multiplicative reduction,
the local heights and (for $`l_•`) the primes ramifying in $`L` and their ramification
indices, such that the image of Galois in $`GL_2(ℤ_{l_◦})` contains $`SL_2(ℤ_{l_◦})`,
the representation into $`GL_2(ℤ_{l_•})` is surjective, and
$`l_◦ ≤ 23040 \cdot 900 d \cdot \mathrm{ht}^{\mathrm{Falt}}([E_L]) + 2 x_{\mathcal{S}} +
C d^{1+ε}`, with the analogous bound for $`l_•` involving
$`6 d \cdot \text{log-diff}_{\overline{\mathcal{M}}_{\mathrm{ell}}}([E_L])`. Uses
{uses "full_galois_actions"}[], {uses "primes_of_prescribed_size"}[],
{uses "elementary_estimates"}[], {uses "faltings_heights_divisor_infinity"}[] and
{uses "log_diff"}[].
:::

:::corollary "full_galois_compactly_bounded"
(Corollary 4.4) For a compactly bounded subset
$`\mathcal{K}_V ⊆ \mathcal{M}_{\mathrm{ell}}(\overline{ℚ})` there are $`C > 0` and a
Galois-finite $`\mathfrak{Exc}` such that every elliptic curve $`E_L` with
$`[E_L] ∈ \mathcal{K}_V \setminus \mathfrak{Exc}` and every finite set of primes
$`\mathcal{S}` admit primes $`l_◦, l_• ∉ \mathcal{S}` with the properties of
{bpref "full_galois_degenerating"}[] and the sharper bounds
$`l_◦ ≤ 23040 \cdot 100 d \cdot \mathrm{ht}^{\mathrm{Falt}}([E_L]) + 2 x_{\mathcal{S}} +
C d`, and analogously for $`l_•`. By Remark 4.4.2, via the $`λ`-line
$`U_ℙ → \mathcal{M}_{\mathrm{ell}} ×_ℤ ℚ`, an entirely similar result holds for the
elliptic curves obtained from points of $`U_ℙ(\overline{ℚ})` in the context of
Theorem 2.1 (ii). Uses {uses "full_galois_actions"}[],
{uses "primes_of_prescribed_size"}[], {uses "elementary_estimates"}[] and
{uses "compactly_bounded_subset"}[].
:::
