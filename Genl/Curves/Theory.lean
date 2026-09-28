/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Genl.GeneralPosition.ProofPackage
import Heights.Curve.CondHeight
import Heights.Curve.Pullback
import Belyi.CurveField.BelyiRelation
import Belyi.CurveField.Tripod
import Belyi.CurveField.CoordRing

/-!
# The height theory of curves over number fields

This file constructs a genuine instance `Genl.Curves.theory` of the abstract height formalism
`Genl.HeightTheory` of [GenEll], §1:

* **curves**: a smooth proper geometrically connected curve `X` over a number field is
  represented by its function field `K` (a finitely generated extension of `ℚ` of transcendence
  degree one, whose constant field is the number field of definition), realised inside the
  algebraically closed field `Ω = AlgebraicClosure (RatFunc ℚ)`
  (`Belyi.CurveField.IsCurveField`); the reduced divisor `D` is a finite set of places of `K`;
  a finite set `G` of generators of the coordinate ring `𝒪(X ∖ D)` fixes the affine integral
  model used for log-conductors ([GenEll], Definition 1.5 (iv), Remark 1.5.1). We consider the
  pairs with `D = ∅` (proper curves) or `D` the set of cusps of a Belyi function
  (`Genl.Curves.Curve`); this class contains the tripod and all proper curves, and is closed
  under the constructions of the proof of [GenEll], Theorem 2.1;
* **points**: `U_X(ℚ̄)` is the set of `ℚ̄`-points (`Belyi.CurveField.QbarPoint`: places with an
  embedding of the residue field into `ℚ̄`) not lying over `D`, filtered by the degree of the
  field of definition;
* **heights**: `ht_{ω_X(D)}` is the Weil height (`Heights.Curve.divHeight`) of the divisor
  `K_X + D`, where `K_X` is the divisor of a differential `dt`
  (`Belyi.CurveField.Divisor.canonicalDiv`) — different `t` give linearly equivalent divisors,
  hence heights in the same BD-class;
* **log-different** and **log-conductor**: `Heights.Curve.logDiff`, `Heights.Curve.logCondOf`;
* **hyperbolicity**: `deg (K_X + D) > 0`;
* **the tripod** `(ℙ¹_ℚ, {0, 1, ∞})`: the rational function field `ℚ(λ) ⊆ Ω` with the three
  cusps of `λ` and the generators `λ, λ⁻¹, (1 − λ)⁻¹` of `ℚ[λ, λ⁻¹, (1 − λ)⁻¹]`;
* **compactly bounded subsets** ([GenEll], Example 1.3 (ii)): for a finite set `V` of primes
  containing `2` and `c ≥ 0`, the points `λ` of the tripod such that at every embedding of
  `ℚ(λ)` into `ℚ̄_p` (`p ∈ V`) and into `ℂ` the image of `λ` lies in the compact domain
  `{z : |log |z|| ≤ c, |log |z − 1|| ≤ c}` of `ℙ¹ ∖ {0, 1, ∞}`.
-/

namespace Genl.Curves

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Curve Heights.Absolute
open scoped IntermediateField

/-- The universal field containing the function fields of all curves over number fields. -/
abbrev Ω : Type := AlgebraicClosure (RatFunc ℚ)

/-- **A curve over a number field with a reduced divisor**, `(X, D)`, together with generators
of the coordinate ring of `X ∖ D` (an affine integral model). `D` is empty or the set of cusps
of a Belyi function. -/
structure Curve where
  /-- The function field of `X`. -/
  K : IntermediateField ℚ Ω
  /-- `K` is the function field of a curve over a number field. -/
  [isCurve : IsCurveField K]
  /-- The reduced divisor `D`, as a finite set of places. -/
  D : Finset (Place K)
  /-- Generators of the coordinate ring `𝒪(X ∖ D)`. -/
  G : Finset K
  /-- `G` generates `𝒪(X ∖ D)` (if `D ≠ ∅`). -/
  G_spec : D.Nonempty → Algebra.adjoin ℚ (G : Set K) = coordRing D
  /-- `D` is empty or the set of cusps of a Belyi function. -/
  cusp : D = ∅ ∨ ∃ φ : K, IsBelyi φ ∧ (D : Set (Place K)) = belyiCusps φ

attribute [instance] Curve.isCurve

namespace Curve

variable (X : Curve)

/-- A separating function `t` used to define the canonical divisor. -/
noncomputable def sep : X.K := Classical.choose (exists_transcendental X.K)

theorem sep_transcendental : Transcendental ℚ X.sep :=
  Classical.choose_spec (exists_transcendental X.K)

/-- The canonical divisor `K_X = div(dt)`. -/
noncomputable def canon : Divisor X.K := canonicalDiv X.sep

/-- The reduced divisor `D` as a divisor. -/
noncomputable def divD : Divisor X.K := ∑ P ∈ X.D, Finsupp.single P 1

/-- The log canonical divisor `K_X + D`. -/
noncomputable def logCanon : Divisor X.K := X.canon + X.divD

/-- The points of `U_X = X ∖ D`. -/
abbrev Pt : Type := {x : QbarPoint X.K // x.P ∉ X.D}

end Curve

/-! ### The tripod -/

/-- The coordinate `λ` of `ℙ¹`, as an element of `Ω`. -/
noncomputable def lam : Ω := algebraMap (RatFunc ℚ) Ω RatFunc.X

theorem lam_transcendental : Transcendental ℚ lam := by
  have hX : Transcendental ℚ (RatFunc.X : RatFunc ℚ) := by
    have h := RatFunc.transcendental_X (K := ℚ)
    convert h using 1
    exact Subsingleton.elim _ _
  exact (transcendental_algebraMap_iff (R := ℚ) (S := RatFunc ℚ) (A := Ω)
    (algebraMap (RatFunc ℚ) Ω).injective (a := RatFunc.X)).mpr hX

/-- The function field `ℚ(λ)` of `ℙ¹_ℚ`. -/
noncomputable def tripodK : IntermediateField ℚ Ω := ℚ⟮lam⟯

/-- The coordinate `λ` in `ℚ(λ)`. -/
noncomputable def tgen : tripodK := IntermediateField.AdjoinSimple.gen ℚ lam

theorem tgen_isRationalGenerator : IsRationalGenerator tgen where
  transcendental := by
    have h := lam_transcendental
    rw [← IntermediateField.AdjoinSimple.algebraMap_gen ℚ lam] at h
    exact (transcendental_algebraMap_iff (algebraMap tripodK Ω).injective).mp h
  adjoin_eq_top := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ y).mp hy
    have hmem : ∀ f : Polynomial ℚ, Polynomial.aeval tgen f ∈ ℚ⟮tgen⟯ := fun f =>
      IntermediateField.algebra_adjoin_le_adjoin ℚ _ (Polynomial.aeval_mem_adjoin_singleton ℚ tgen)
    have h : (⟨Polynomial.aeval lam r / Polynomial.aeval lam s, hy⟩ : tripodK) =
        Polynomial.aeval tgen r / Polynomial.aeval tgen s := by
      apply Subtype.ext
      change _ = ((Polynomial.aeval tgen r : tripodK) : Ω) /
        ((Polynomial.aeval tgen s : tripodK) : Ω)
      have h1 : ∀ f : Polynomial ℚ, ((Polynomial.aeval tgen f : tripodK) : Ω) =
          Polynomial.aeval lam f := fun f =>
        (Polynomial.aeval_algHom_apply (IntermediateField.val tripodK) tgen f).symm
      rw [h1, h1]
    rw [h]
    exact div_mem (hmem r) (hmem s)

instance : IsCurveField tripodK := tgen_isRationalGenerator.isCurveField

open Classical in
/-- **The tripod** `(ℙ¹_ℚ, {0, 1, ∞})` with the model `ℚ[λ, λ⁻¹, (1 − λ)⁻¹]`. -/
@[reducible] noncomputable def tripod : Curve where
  K := tripodK
  D := tripodPlaces tgen
  G := {tgen, tgen⁻¹, (1 - tgen)⁻¹}
  G_spec _ := by
    apply SetLike.ext'
    rw [coordRing]
    change (Algebra.adjoin ℚ ((({tgen, tgen⁻¹, (1 - tgen)⁻¹} : Finset tripodK) : Set tripodK)) :
      Set tripodK) = {f | ∀ P : Place tripodK, P ∉ tripodPlaces tgen → f ∈ P.1}
    rw [setOf_forall_mem_eq_adjoin_tripod tgen_isRationalGenerator]
    simp
  cusp := Or.inr ⟨tgen, ⟨tgen_isRationalGenerator.transcendental, fun P hP => by
      rw [ramIdx_eq_one_of_adjoin_eq_top tgen_isRationalGenerator.transcendental
        tgen_isRationalGenerator.adjoin_eq_top] at hP
      exact absurd hP (lt_irrefl 1)⟩, by
      ext P
      rw [Finset.mem_coe, mem_tripodPlaces_iff_ord tgen_isRationalGenerator]
      rfl⟩

theorem tripod_K : tripod.K = tripodK := rfl

theorem tripod_D : tripod.D = tripodPlaces tgen := rfl

/-- The coordinate `λ` is regular at the points of the tripod. -/
theorem tgen_mem (x : tripod.Pt) : tgen ∈ x.1.P.1 :=
  mem_of_notMem_tripodPlaces tgen_isRationalGenerator x.2

/-- The value `λ(x) ∈ ℚ(x)` of a point of the tripod. -/
noncomputable def tripodValue (x : tripod.Pt) : x.1.fieldOf := evalF x.1 ⟨tgen, tgen_mem x⟩

/-! ### Compactly bounded subsets -/

/-- Primes carry their primality as an instance (local). -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The data of a compactly bounded subset of the tripod ([GenEll], Example 1.3 (ii)): a finite
set `V` of primes containing `2` (so `V ∪ {∞}` contains the support `Σ = {2}` and the archimedean
place) and a bound `c` defining the compact domains
`{z ∈ ℙ¹(ℚ̄_v) : |log |z|_v| ≤ c, |log |z − 1|_v| ≤ c}` of `U_ℙ(ℚ̄_v)`. -/
structure CBSData where
  /-- The nonarchimedean part of the support. -/
  V : Finset Nat.Primes
  /-- The support contains `2`. -/
  two_mem : (⟨2, Nat.prime_two⟩ : Nat.Primes) ∈ V
  /-- The bound. -/
  c : ℝ

/-- The compactly bounded subset: the points of the tripod all of whose conjugates at the places
of `V ∪ {∞}` lie in the bounding domains. -/
def CBSData.set (B : CBSData) : Set tripod.Pt :=
  {x | (∀ p ∈ B.V, ∀ τ : x.1.fieldOf →+* PadicAlgCl (p : ℕ),
      |Real.log ‖τ (tripodValue x)‖| ≤ B.c ∧ |Real.log ‖τ (tripodValue x) - 1‖| ≤ B.c) ∧
    ∀ σ : x.1.fieldOf →+* ℂ,
      |Real.log ‖σ (tripodValue x)‖| ≤ B.c ∧ |Real.log ‖σ (tripodValue x) - 1‖| ≤ B.c}

/-! ### The height theory -/

theorem deg_divD (X : Curve) : X.divD.deg = ∑ P ∈ X.D, (P.deg : ℤ) := by
  rw [Curve.divD, ← degHom_apply, map_sum]
  simp [deg_single]

theorem deg_canon_tripod : tripod.canon.deg = -2 := by
  rw [Curve.canon, deg_canonicalDiv_eq tripod.sep_transcendental
    tgen_isRationalGenerator.transcendental]
  exact deg_canonicalDiv_of_adjoin_eq_top tgen_isRationalGenerator.transcendental
    tgen_isRationalGenerator.adjoin_eq_top

theorem deg_logCanon_tripod : tripod.logCanon.deg = 1 := by
  rw [Curve.logCanon, deg_add, deg_canon_tripod, deg_divD]
  have : ∑ P ∈ tripod.D, (P.deg : ℤ) = 3 := by
    have h1 : ∀ P ∈ tripod.D, (P.deg : ℤ) = 1 := fun P hP => by
      have := deg_of_mem_tripodPlaces tgen_isRationalGenerator (P := P) hP
      exact_mod_cast this
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_tripodPlaces tgen_isRationalGenerator
  rw [this]
  norm_num

open Classical in
/-- **The height theory of curves over number fields** ([GenEll], §1). -/
noncomputable def theory : HeightTheory.{0} where
  Curve := Curve
  Pt X := X.Pt
  Hyperbolic X := 0 < X.logCanon.deg
  DivisorFree X := X.D = ∅
  ptLE X d := {x | x.1.deg ≤ d}
  ptEQ X d := {x | x.1.deg = d}
  ptLE_zero X := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact x.1.deg_pos
  ptLE_succ X d := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    omega
  htCan X x := divHeight X.logCanon x.1
  logDiff X x := Heights.Curve.logDiff x.1
  logCond X x := if X.D = ∅ then 0 else logCondOf X.G x.1
  tripod := tripod
  hyperbolic_tripod := by
    change 0 < tripod.logCanon.deg
    rw [deg_logCanon_tripod]
    exact one_pos
  CBS := CBSData
  cbsSet := CBSData.set

@[simp] theorem theory_htCan (X : Curve) (x : X.Pt) :
    theory.htCan X x = divHeight X.logCanon x.1 := rfl

@[simp] theorem theory_logDiff (X : Curve) (x : X.Pt) :
    theory.logDiff X x = Heights.Curve.logDiff x.1 := rfl

theorem theory_logCond_of_nonempty (X : Curve) (hD : X.D.Nonempty) (x : X.Pt) :
    theory.logCond X x = logCondOf X.G x.1 := by
  classical
  change (if X.D = ∅ then 0 else logCondOf X.G x.1) = _
  rw [if_neg hD.ne_empty]

theorem theory_logCond_of_eq_empty (X : Curve) (hD : X.D = ∅) (x : X.Pt) :
    theory.logCond X x = 0 := by
  classical
  change (if X.D = ∅ then 0 else logCondOf X.G x.1) = _
  rw [if_pos hD]

end Genl.Curves
