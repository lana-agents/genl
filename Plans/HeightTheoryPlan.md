# A real `Genl.HeightTheory` and its `ProofPackage` — design and plan

Branch `wp-height-theory` (genl, heights, belyi, iut). Status as of 2026-09-27.

## 0. Goal

`Genl.HeightTheory.statementII_implies_statementI` proves [GenEll] Theorem 2.1 (ii) ⇒ (i)
for any `T : HeightTheory` with `A : T.ProofPackage`. The ABC programme (iut) proves
`Iut.Tripod.tripodTheory.StatementII` (conditionally on the Cor 3.12 variant) and needs
`tripodTheory.StatementI`. We need a genuine height theory `T` of curves over number fields
with

1. `tripodTheory.StatementII → T.StatementII` (tripod dictionary),
2. `A : T.ProofPackage` (all fields proved for the genuine objects),
3. `T.StatementI → tripodTheory.StatementI` (tripod dictionary).

Final deliverable (iut): `Iut.Tripod.statementI_of_statementII :
tripodTheory.StatementII → tripodTheory.StatementI`, with no hypotheses.

## 1. Correction of the genl interface (done: genl `3a470a9`)

`BelyiDescent.htE_equiv : htE ≈[Ξ] q • T.htCan X` with `q = deg E / deg ω_X` is **false**
for genuine heights: `ht_E − q·ht_{ω_X}` is (up to `O(1)`) the height of the degree-0 class
`E − q·K_X ∈ Pic(X) ⊗ ℚ`, which is unbounded in both directions on `X(ℚ̄)^{=d}` unless the
class is torsion (Néron–Tate). Replaced by `htE_le : htE ≲[Ξ] q • T.htCan X` with `q` any
real `> deg E / deg ω_X` (true by Prop. 1.4: positive degree ⇒ height bounded below). The
proof of Theorem 2.1 only used `htE_equiv.le`; `TheoremTwoOne.lean` is unchanged otherwise.
All other fields of `Covering`/`BelyiDescent` were checked to be true for genuine objects
(see §4 for the proofs planned for each).

## 2. Design decisions

### 2.1 Curves = function fields (not schemes)

A smooth proper geometrically connected curve over a number field is the same as a field
`K ⊇ ℚ`, finitely generated of transcendence degree 1 (its constant field `k` = algebraic
closure of `ℚ` in `K` is a number field; `X` = the regular projective model). We represent
curves by function fields, concretely as intermediate fields `K ⊆ Ω := AlgebraicClosure
(RatFunc ℚ)` (every such field embeds in `Ω`; this keeps `Curve : Type` so that
`T : HeightTheory.{0}` like `tripodTheory`). All general theory is stated for an abstract
`[Field K] [CharZero K]` with the finiteness hypotheses, and specialised.

Why not schemes (as in belyi): the Weil height machine needs line bundles/divisors up to
linear equivalence, global sections, pull-back along finite maps, degrees, a canonical
divisor, Riemann–Hurwitz, and the existence of functions with prescribed poles (Riemann's
theorem). None of this exists for Mathlib schemes (no Picard group of curves, no
cohomology/Riemann–Roch, no Kähler differentials of schemes in usable form), while for
function fields everything reduces to Dedekind-domain theory, which Mathlib has in depth
(`HeightOneSpectrum`, adic valuations, `Ideal.ramificationIdx`/`inertiaDeg`,
`sum_ramification_inertia_eq_finrank` = fundamental identity, `differentIdeal` with
`pow_sub_one_dvd_differentIdeal`, `aeval_derivative_mem_differentIdeal`,
`dvd_differentIdeal_iff`), plus valuation-subring theory
(`iInf_valuationSubring_superset`: integral closure = ⋂ of valuation subrings; Chevalley
extension `IsLocalRing.exists_factor_valuationRing`). The belyi repository's scheme curves
are linked by a bridge `X ↦ X.functionField` (node C11, not on the critical path);
noncritical Belyi maps are formulated on function fields, so they and the height machine
share the same objects.

### 2.2 Places, points, divisors

* `Place K` := valuation subrings `O ⊊ K` (automatically `⊇ ℚ`, since residue fields have
  characteristic 0 for places we use; the definition does not need it). Discreteness,
  finiteness of residue fields over `ℚ`, and degrees come from the Dedekind *charts*: for
  `t ∈ K` transcendental, the integral closures `A_t`, `A_{1/t}` of `ℚ[t]`, `ℚ[1/t]` in `K`
  are Dedekind and finite; every place is a localisation of one of them at a height-one
  prime (a valuation ring dominating a DVR with the same fraction field equals it).
* A point `x ∈ X(ℚ̄)` = a place `O_x` with a ring map `σ_x : O_x → ℚ̄ := AlgebraicClosure ℚ`
  with kernel the maximal ideal (this is `Hom(Spec ℚ̄, X)` for the regular proper model;
  it includes the embedding of the constant field). `f(x) := σ_x f ∈ ℚ̄` for `f ∈ O_x`,
  `∞` otherwise. Minimal field of definition `F_x := σ_x(O_x)` (an intermediate field of
  `ℚ̄/ℚ`), `deg x := [F_x : ℚ]`.
* `Div K := Place K →₀ ℤ`, `deg P := [κ(P) : ℚ]` (degrees over `ℚ`; degrees over the
  constant field differ by the factor `[k : ℚ]`, which does not affect signs or ratios).

### 2.3 Heights (Weil machine without line bundles)

* Absolute logarithmic height `h : ℙⁿ(ℚ̄) → ℝ` (via any number field containing the
  coordinates; invariance under extension of the field).
* For a tuple `s : Fin (m+1) → K` (not all 0) and a point `x`: choose `i₀` with
  `v_x(s_{i₀})` minimal (valuation rings are totally ordered, so it exists); all
  `s_i/s_{i₀} ∈ O_x`, set `h_s(x) := h([(s_i/s_{i₀})(x)]_i)`. No base-point condition is
  needed: `h_s` is the height attached to `A_s := −min_i div(s_i)`.
* **Integrality lemma** (the only analytic input): if `t ∈ K` lies in every valuation
  subring containing `ℚ[r_1, …, r_n]`, then `t` is integral over it
  (`iInf_valuationSubring_superset`), hence there are a finite set `S` of primes and
  `C ≥ 1` with `|t(x)|_w ≤ C_w · max(1, max_j |r_j(x)|_w)^M` for all points and places, and
  `C_w = 1` for `w ∤ S∞`.
* Consequences: `A_s = A_{s'}` ⇒ `h_s ≈ h_{s'}`; `h_{rs} = h_s`; Segre: `h_{s⊗s'} = h_s +
  h_{s'}`; pull-back along `K ⊆ L` is exact. Divisor heights: by Riemann's theorem every
  divisor is `A ~ A_s − A_{s'}`, and `ht_A := h_s − h_{s'}` is well defined up to BD,
  additive, functorial, `ht_{div f} ≈ 0`, `ht_{(f)_∞} ≈ h(f)`, and
  `deg A > 0 ⇒ ht_A ≳ 0`.

### 2.4 Canonical divisor, log-different, log-conductor

* `K_X := div(dt)`: for a place `P` with uniformiser `π`, `D_π` = the unique derivation of
  `K` with `D_π π = 1`; `v_P(dt) := v_P(D_π t)`. Key lemma `D_π(O_P) ⊆ O_P`; chain rule by
  uniqueness of derivations. Riemann–Hurwitz (characteristic 0, all ramification tame):
  `div_L(dt) = π^* div_K(dt) + Σ (e_Q − 1) Q`.
* `htCan X := ht_{K_X + D}`, `Hyperbolic X :⇔ deg(K_X + D) > 0`, `DivisorFree X :⇔ D = ∅`.
* `logDiff X x := log|disc F_x| / [F_x : ℚ]` (same formula as `Iut.Tripod.logDiff`).
* `logCond X x` := `(1/[F_x:ℚ]) Σ log N(w)` over the finite places `w` of `F_x` with
  `max_i |g_i(x)|_w > 1`, where `g_1, …, g_r` generate the coordinate ring `𝒪(U_X)`
  (the model = closure of `U_X ↪ 𝔸^r`, as in [GenEll] Def. 1.5(iv)); `0` if `D = ∅`. Its
  BD-class does not depend on the generators (Remark 1.5.1; node W6). For the tripod with
  `g = (λ, λ⁻¹, (1−λ)⁻¹)` this is literally `Iut.Tripod.logCond`.

### 2.5 The curve class of `T`

`T.Curve` := pairs `(K, D)` with `D = ∅` or `D = E_φ := φ⁻¹{0,1,∞}_red` for a Belyi function
`φ ∈ K` (all ramification of `K/ℚ(φ)` over `{0,1,∞}`) — *Belyi-cuspidal pairs*. This class
contains the tripod `(ℚ(λ), E_λ)` and every proper curve, and is closed under what the
proof package needs:

* `covering` for `(K, E_φ)`: `L = K(u, v) ⊆ Ω`, `u^N = φ`, `v^N = 1 − φ` (pull-back of the
  Fermat curve); étale over `U_X` (discriminant `N^N φ^{N-1}` is a unit off `E_φ`),
  ramification `≥ N / deg φ` over `E_φ` (valuation divisibility), so
  `deg π^*(K_X + E) / deg K_Y → 1`. For the tripod, `L` is the Fermat curve.
  For `D = ∅`: `Y = X`, `π = id`.
* `belyi` for proper `X`: noncritical Belyi maps (node C9) + compactness (node W8).

The full class of all pairs `(X, D)` needs, for `covering`, the existence of coverings with
prescribed ramification over an arbitrary `D` (Fox's theorem on surface groups + Riemann
existence (oka) + descent from `ℂ` to a number field (belyi `Converse/*`)); recorded as node
F1, not on the ABC path. `T.StatementI` for the Belyi-cuspidal class already contains the
effective Mordell/Vojta statement for all proper hyperbolic curves and the tripod ABC.

### 2.6 Compactly bounded subsets

`T.CBS` := `(V, c)` with `V` a finite set of primes containing `2` (i.e. `Σ = {2}`) and the
set of points `λ` of the tripod with `|log|λ|_w|, |log|λ−1|_w| ≤ c` at all places of `F_λ`
over `V ∪ {∞}` — the same family as `Iut.Tripod.CompactlyBounded`. Each is a compactly
bounded subset in the sense of [GenEll] Example 1.3(ii) (bounding domains
`{|log|z||, |log|z−1|| ≤ c}`, compact domains in `U_ℙ`), and they are cofinal among the
compactly bounded subsets with bounding domains in `U_ℙ` (node W11, optional sanity).

### 2.7 The compactness argument without topology on `X(ℚ̄_v)`

Given `x_n ∈ X(ℚ̄)^{=d}` and `v ∈ V`, index the `d` embeddings `F_{x_n} → ℚ̄_v` (`ℚ̄_p =
PadicAlgCl p`, or `ℂ`). By sequential compactness of `ℙ¹(ℚ̄_p)^{≤d}` (monic polynomials with
`ℤ_p`-coefficients + continuity of roots) and of `ℙ¹(ℂ)`, and a diagonal argument over the
countable field `K`, pass to a subsequence along which `f(x_n^σ)` converges in `ℙ¹` for every
`f ∈ K`. The limit `ξ : K → ℙ¹(ℚ̄_v)` is a place: `O_ξ := {f | ξ f ≠ ∞}` is a valuation
subring, either `K` (then `ξ(φ) ∉ {0,1,∞}` for every nonconstant `φ`) or a place `P_ξ`.
Choose a Belyi map `φ` with `E_φ ∩ {P_ξ} = ∅` (noncritical Belyi); then `φ(x_n^σ) → ξ(φ)
∉ {0,1,∞}`, so a tail of the sequence lies in a valuation-bounded `K_V`.

## 3. Repositories and dependency chain

```
Mathlib v4.32 ── belyi (wp-height-theory: Belyi/FunctionField/*)          curve theory
                   └─ heights (wp-height-theory: Heights/Absolute/*,      height machine
                             Heights/Curve/*; depends on belyi)
                        └─ genl fork (wp-height-theory: Genl/Curves/*)     T, ProofPackage
                             └─ iut (wp-height-theory worktree: Iut/GenEll/*) dictionary
```

`heights` requires `belyi` only for `Belyi.FunctionField.*`, which imports Mathlib only (the
`oka` package is fetched but not built). The Serre different bound and the finite-height
extension lemma currently in iut (`Iut/Tower/SerreBound.lean`, `Iut.finHeight_algebraMap`)
are ported to heights (with attribution) because genl cannot depend on iut.

## 4. Lemma DAG

Estimates are Lean lines (proof + statements), `✓` = done.

### belyi — curve theory (`Belyi/FunctionField/`)

| id | content | deps | est |
|----|---------|------|-----|
| C1 | `Place K`; `O_P` DVR, `v_P : K^× → ℤ`, `κ(P)` finite over `ℚ`, via Dedekind charts `A_t`, `A_{1/t}`; places ↔ `HeightOneSpectrum A_t ⊔ HeightOneSpectrum A_{1/t}` over `1/t` | Mathlib | 1500 |
| C2 | divisors, `div f`, `(f)_0`, `(f)_∞`, finiteness; fundamental identity `deg (t)_∞ = [K : ℚ(t)]`; `deg div f = 0` | C1 | 900 |
| C3 | `QbarPoint K` = `(O, σ)`; evaluation; `F_x`, `deg x`; lifting of points along finite `K ⊆ L` with `deg y ≤ [L:K]·deg x`; finiteness of points over a place | C1 | 700 |
| C4 | Riemann spaces `L(A)` finite-dim, `ℓ(A) ≤ deg A + ℓ(0)`, Riemann's theorem `ℓ(A) ≥ deg A + const`, equality for `deg A ≫ 0`; realisation: `deg A ≫ 0`, `A ≥ 0` ⇒ `∃ f, (f)_∞ = A`; weak approximation | C1,C2 | 2500 |
| C5 | derivations `D_π`, `D_π(O_P) ⊆ O_P`, `div(dt)`, canonical class, chain rule | C1,C2 | 1500 |
| C6 | Riemann–Hurwitz for `K ⊆ L` (char 0), `e_Q = v_Q(π_P)`, `Σ_{Q∣P} e_Q f_Q = [L:K]` | C5 | 800 |
| C7 | Belyi functions, `E_φ`, `K_X + E_φ ~ φ^*[∞]` | C6 | 400 |
| C8 | Kummer–Fermat covers `K(u,v)`: unramified off `E_φ`, `e ≥ N/deg φ` over `E_φ`, hyperbolicity and degree ratio | C6,C7 | 1200 |
| C9a | ℙ¹ part of [NCB] (Mochizuki, *Noncritical Belyi maps*, 2004) Lemmas 2.1–2.4: `S ⊆ ℙ¹(ℚ̄)` finite Galois-stable, `τ ∈ ℙ¹(ℚ) ∖ S` ⇒ a composite `H` of rational Möbius maps and rational polynomials with `H(S) ⊆ {0,1,∞}`, `H(τ) ∉ {0,1,∞}`, `H` unramified over `ℙ¹ ∖ {0,1,∞}`. Genericity is avoided: all choices are made by archimedean size estimates (`τ` made huge, `x^m(x−1)^n` monotone on `x > 1`) | Mathlib | 2500 |
| C9b | [NCB] Thm 2.5, curve step: for a finite set `T` of places, enlarge `T` so that `D := Σ_{t∈T} t` has large degree; by Riemann (C4) pick `f ∈ L(D) ∖ ⋃_t L(D − t)`; then `ψ := 1/f` has `(ψ)_0 = D`, so `ψ(T) = 0` with `ψ` unramified over `0`. Branch values of `ψ` form a Galois-stable finite set not containing `0` | C4,C6 | 800 |
| C9 | noncritical Belyi maps: `∀ T` finite set of places, `∃ φ` Belyi with `T ∩ E_φ = ∅` (`φ = H(ψ)`; ramification multiplicative in the tower `K ⊇ ℚ(ψ) ⊇ ℚ(φ)`) | C9a,C9b,C7 | 600 |
| C11 | bridge to belyi's scheme curves (`X ↦ X.functionField`, closed points ↔ places) | C1 | 1500 (optional) |

### heights — absolute heights and the machine on curves

| id | content | deps | est |
|----|---------|------|-----|
| H1 | absolute log height on `ℙⁿ(ℚ̄)`: well defined (extension invariance at finite and infinite places), scaling, Galois invariance, `h ≥ 0`, Segre identity, `h(a) = h([1:a])` agrees with `Iut.Tripod.htCan` | Mathlib | 900 |
| H2 | local root bounds (`|root|_w ≤ C_w max|coeff|_w`, `C_w = 1` at `w ∤ ∞` for monic integral) | Mathlib | 300 |
| H3 | Northcott for bounded degree over `ℚ̄` (discharges `Iut.Tripod.NorthcottHyp`; not needed for the package) | H1 | 800 (optional) |
| W1 | tuple heights `h_s`, `h_{rs} = h_s`, Segre additivity, exact pull-back | H1,C3 | 600 |
| W2 | integrality lemma ⇒ `A_s = A_{s'} ⇒ h_s ≈ h_{s'}` | W1,H2 | 800 |
| W3 | divisor heights `ht_A` (BD-classes), additivity, functoriality, `ht_{div f} ≈ 0`, `ht_{(f)_∞} ≈ h∘f` | W2,C4 | 700 |
| W4 | positivity: `deg A > 0 ⇒ ht_A ≳ 0`; `deg A < q deg B ⇒ ht_A ≲ q ht_B` | W3,C4 | 400 |
| W5 | `logDiff`, `logCond` (w.r.t. generators); BD-independence of generators; Prop 1.6 `log-cond_D ≲ ht_D` | W2,C3 | 1000 |
| W6 | different tower formula `log-diff_X(x) − log-diff(y) = normalised rel. different`; Serre bound port | Mathlib | 800 |
| W7a | Prop 1.7(i), Belyi case (`e = 1`): `log-diff_ℙ∘φ + log-cond_C∘φ ≲ log-diff_X + log-cond_E` | W5,W6,C7 | 900 |
| W7b | Prop 1.7(i), Kummer–Fermat case: `log-diff_Y ≲ log-diff_X∘π + log-cond_E∘π` | W5,W6,C8 | 1200 |
| W8 | compactness: sequential compactness of `ℙ¹(ℚ̄_p)^{≤d}`, `ℙ¹(ℂ)`; limit places; CBS from noncritical `φ` | C3,C9 | 1800 |
| W11 | cofinality of the valuation-bounded CBS (sanity, optional) | W8 | 600 |

### genl fork — the theory and the package (`Genl/Curves/`)

| id | content | deps | est |
|----|---------|------|-----|
| G1 | `Genl.Curves.theory : HeightTheory` (Belyi-cuspidal pairs in `Ω`, points `U_X(ℚ̄)`, `htCan = ht_{K_X+D}`, `logDiff`, `logCond`, tripod, CBS) | W3,W5,C7 | 500 |
| G2 | `covering` (Fermat pull-back / identity): `surjOn` (C3), `logDiff_le` (W7b), `htCan_le` (W4,C8) | C8,W4,W7b | 800 |
| G3 | `belyi`: failure sequence, W8, C9, `htCan_equiv` (C7,W3), `logDiff_comp_le` (W7a), `logCondE_le` (W5), `htE_le` (W4) | W8,C9,W7a | 900 |

### iut — dictionary and assembly (`Iut/GenEll/`)

| id | content | deps | est |
|----|---------|------|-----|
| I1 | tripod points `≃ Iut.Tripod.Pt` preserving degree; `htCan ≈`, `logDiff =`, `logCond =` (with the generators `λ, λ⁻¹, (1−λ)⁻¹`), `cbsSet` equal | G1 | 600 |
| I2 | `tripodTheory.StatementII → T.StatementII`; `T.StatementI → tripodTheory.StatementI`; final theorem | I1,G2,G3 | 200 |

### Off the ABC path

| id | content | est |
|----|---------|-----|
| F1 | coverings with ramification `≥ e` over an arbitrary reduced `D` (Fox + Riemann existence + descent) ⇒ `T` for all pairs `(X, D)` | 8000+ |

## 5. Estimate

Critical path C1→C2→C4→(W2,W3,W4)→C5→C6→C8→W7b→G2 and C9a/C9b→C9→W8→G3→I2.
Total ≈ 30–36k lines on the ABC path (≈ 38–46k with the optional nodes). The largest risks
are C4 (Riemann's theorem from scratch), C5 (derivations on function fields) and C9a (many
small real-inequality lemmas; the construction itself is explicit, following [NCB]). A realistic
schedule with one lead and parallel sub-agents is 4–8 weeks of continuous work.

## 6. Progress log

* 2026-09-27: design (this file); genl interface correction `htE_equiv → htE_le`.
