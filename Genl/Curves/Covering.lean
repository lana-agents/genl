/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Genl.Curves.BelyiDescent
import Heights.Curve.KummerPoint
import Heights.Curve.ModelChange
import Belyi.CurveField.Kummer

/-!
# Coverings ramified over the divisor

For the height theory `Genl.Curves.theory` of curves over number fields, this file constructs
the output `Genl.HeightTheory.Covering` of the first paragraph of the proof of [GenEll],
Theorem 2.1: a divisor free hyperbolic curve `Y` with a finite map `Y → X`, along which points
lift with bounded degree, `log-diff_Y ≲ log-diff_X + log-cond_D` and
`ht_{ω_X(D)} ≲ (1 + ε') ht_{ω_Y}`.

* If `D = ∅`, `Y = X` works (`Genl.Curves.coveringOfDivisorFree`): heights of the positive
  degree divisor `K_X` are bounded below.
* If `D` is the set of cusps of a Belyi function `φ`, `Y` is the **Kummer–Fermat covering**
  `u^N = φ`, `v^N = 1 − φ` (`Genl.Curves.fermatCurve`), whose function field is
  `K(u, v) ⊆ Ω`. Over every cusp the ramification index is at least `N / M`
  (`Belyi.CurveField.Place.le_ramificationIdx_mul_abs_ord`), so by Riemann–Hurwitz
  `deg (π^* (K_X + D)) < (1 + ε') deg K_Y` for `N` large (Propositions 1.4 (i), (ii), (iii) of
  [GenEll] then give `ht_{ω_X(D)} ∘ π ≲ (1 + ε') ht_{ω_Y}`); the field of definition of a point
  `y` over `x ∉ D` is `ℚ(x)(u(y), v(y))`, and the discriminant bound for such Kummer extensions
  (`Heights.Curve.logDisc_le_of_eq_adjoin`) together with the model independence of
  log-conductors gives `log-diff_Y ≲ log-diff_X + log-cond_D` ([GenEll], Proposition 1.7 (i)).
  The finitely many points of `Y` over `D` do not matter.
-/

namespace Genl.Curves

open Belyi.CurveField Belyi.CurveField.Divisor Heights.Curve Heights.Absolute Module

open Classical in
/-- **The covering for a divisor free curve** is the identity. -/
noncomputable def coveringOfDivisorFree (X : Curve) (hX : theory.Hyperbolic X)
    (hD : theory.DivisorFree X) (d : ℕ) (ε' : ℝ) (hε' : 0 < ε') : theory.Covering X d ε' where
  Y := X
  hyperbolic := hX
  divisorFree := hD
  d' := d
  π := id
  surjOn := fun x hx => ⟨x, hx, rfl⟩
  logDiff_le := ⟨0, fun x _ => by
    change logDiff x.1 ≤ logDiff x.1 + (if X.D = ∅ then 0 else logCondOf X.G x.1) + 0
    rw [if_pos (show X.D = ∅ from hD)]
    simp⟩
  htCan_le := by
    obtain ⟨C, hC⟩ := divHeight_bddBelow (show 0 < X.logCanon.deg from hX)
    refine ⟨ε' * C, fun x _ => ?_⟩
    change divHeight X.logCanon x.1 ≤ (1 + ε') * divHeight X.logCanon x.1 + ε' * C
    have := hC x.1
    nlinarith

/-! ### A Riemann–Hurwitz inequality -/

section Hurwitz

variable {K L : Type*} [Field K] [CharZero K] [IsCurveField K] [Field L] [CharZero L]
  [IsCurveField L] [Algebra K L] [FiniteDimensional K L]

/-- If the ramification indices over a reduced divisor `A` are at least `e`, then
`(e - 1) deg (π^* A) ≤ e deg R_{L/K}`. -/
theorem sub_one_mul_deg_pullback_le (A : Divisor K) (hA0 : 0 ≤ A) (hA1 : ∀ P, A P ≤ 1)
    (e : ℕ) (he : ∀ Q : Place L, A (Q.restrict K) ≠ 0 → e ≤ Q.ramificationIdx K) :
    ((e : ℤ) - 1) * (pullback L A).deg ≤ e * (relRamDiv K L).deg := by
  have hle : ((e : ℤ) - 1) • pullback L A ≤ (e : ℤ) • relRamDiv K L := by
    intro Q
    simp only [Finsupp.smul_apply, smul_eq_mul, pullback_apply, relRamDiv_apply]
    have h0 := hA0 (Q.restrict K)
    have h1 := hA1 (Q.restrict K)
    simp only [Finsupp.coe_zero, Pi.zero_apply] at h0
    have hpos : (1 : ℤ) ≤ Q.ramificationIdx K := by exact_mod_cast Q.ramificationIdx_pos
    have he0 : (0 : ℤ) ≤ e := Nat.cast_nonneg _
    rcases (show A (Q.restrict K) = 0 ∨ A (Q.restrict K) = 1 by omega) with h | h
    · rw [h, mul_zero, mul_zero]
      nlinarith
    · have h2 := he Q (by rw [h]; exact one_ne_zero)
      have h3 : (e : ℤ) ≤ Q.ramificationIdx K := by exact_mod_cast h2
      rw [h, mul_one]
      nlinarith
  have := deg_mono hle
  rwa [← degHom_apply, ← degHom_apply, map_zsmul, map_zsmul, degHom_apply, degHom_apply,
    smul_eq_mul, smul_eq_mul] at this

end Hurwitz

/-! ### Kummer–Fermat coverings of curves -/

section Fermat

variable (X : Curve) (φ : X.K) {N : ℕ} (hN : 0 < N)

/-- An `N`-th root `u` of `φ` in `Ω`. -/
noncomputable def fermatU : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq ((φ : X.K) : Ω) hN)

theorem fermatU_pow : fermatU X φ hN ^ N = (φ : Ω) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((φ : X.K) : Ω) hN)

/-- An `N`-th root `v` of `1 - φ` in `Ω`. -/
noncomputable def fermatV : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (1 - ((φ : X.K) : Ω)) hN)

theorem fermatV_pow : fermatV X φ hN ^ N = 1 - (φ : Ω) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (1 - ((φ : X.K) : Ω)) hN)

/-- The function field `K(u, v)` of the Kummer–Fermat covering, as an extension of `K`. -/
noncomputable def fermatE : IntermediateField X.K Ω :=
  IntermediateField.adjoin X.K {fermatU X φ hN, fermatV X φ hN}

/-- The function field `K(u, v)` of the Kummer–Fermat covering. -/
noncomputable def fermatField : IntermediateField ℚ Ω := (fermatE X φ hN).restrictScalars ℚ

noncomputable instance : Algebra X.K (fermatField X φ hN) :=
  inferInstanceAs (Algebra X.K (fermatE X φ hN))

omit hN in
theorem isIntegral_of_pow_eq (hN' : 0 < N) {a : Ω} {b : X.K} (h : a ^ N = (b : Ω)) :
    IsIntegral X.K a :=
  IsIntegral.of_pow hN' (by rw [h]; exact isIntegral_algebraMap (x := b))

instance : FiniteDimensional X.K (fermatField X φ hN) := by
  have : FiniteDimensional X.K (fermatE X φ hN) := by
    refine IntermediateField.finiteDimensional_adjoin fun a ha => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact isIntegral_of_pow_eq X hN (fermatU_pow X φ hN)
    · exact isIntegral_of_pow_eq X hN (b := 1 - φ) (by rw [fermatV_pow]; simp)
  exact inferInstanceAs (FiniteDimensional X.K (fermatE X φ hN))

instance : IsCurveField (fermatField X φ hN) := isCurveField_of_finite X.K _

/-- `u` as an element of `K(u, v)`. -/
noncomputable def fermatU' : fermatField X φ hN :=
  ⟨fermatU X φ hN, IntermediateField.subset_adjoin X.K _ (by simp)⟩

/-- `v` as an element of `K(u, v)`. -/
noncomputable def fermatV' : fermatField X φ hN :=
  ⟨fermatV X φ hN, IntermediateField.subset_adjoin X.K _ (by simp)⟩

theorem fermatU'_pow : fermatU' X φ hN ^ N = algebraMap X.K (fermatField X φ hN) φ :=
  Subtype.ext (fermatU_pow X φ hN)

theorem fermatV'_pow : fermatV' X φ hN ^ N = 1 - algebraMap X.K (fermatField X φ hN) φ :=
  Subtype.ext (fermatV_pow X φ hN)

theorem adjoin_fermat_eq_top :
    IntermediateField.adjoin X.K {fermatU' X φ hN, fermatV' X φ hN} = ⊤ := by
  let ι : fermatField X φ hN →ₐ[X.K] Ω := (fermatE X φ hN).val
  have hmap : (IntermediateField.adjoin X.K {fermatU' X φ hN, fermatV' X φ hN}).map ι =
      fermatE X φ hN := by
    rw [IntermediateField.adjoin_map, Set.image_insert_eq, Set.image_singleton]
    rfl
  rw [eq_top_iff]
  rintro z -
  have hz : (z : Ω) ∈ fermatE X φ hN := z.2
  rw [← hmap] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = z := Subtype.ext hwz
  rwa [← this]

theorem finrank_fermat_pos : 0 < finrank X.K (fermatField X φ hN) := by
  have : Module.IsTorsionFree X.K (fermatField X φ hN) :=
    DivisionSemiring.to_moduleIsTorsionFree
  exact Module.finrank_pos

/-- **The Kummer–Fermat covering** `Y : u^N = φ, v^N = 1 − φ` of `X`, as a divisor free
curve. -/
@[reducible] noncomputable def fermatCurve : Curve where
  K := fermatField X φ hN
  isCurve := isCurveField_of_finite X.K _
  D := ∅
  G := ∅
  G_spec h := absurd h Finset.not_nonempty_empty
  cusp := Or.inl rfl

end Fermat

/-! ### The covering for curves with cusps -/

theorem divD_apply (X : Curve) (P : Place X.K) [Decidable (P ∈ X.D)] :
    X.divD P = if P ∈ X.D then 1 else 0 := by
  classical
  rw [Curve.divD, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  congr

theorem divD_nonneg (X : Curve) : 0 ≤ X.divD := fun P => by
  classical
  rw [divD_apply]
  split_ifs <;> simp

theorem divD_le_one (X : Curve) (P : Place X.K) : X.divD P ≤ 1 := by
  classical
  rw [divD_apply]
  split_ifs <;> simp

/-- A curve whose divisor is the set of cusps of a Belyi function has points off the
divisor: the points where `φ = 2`. -/
theorem nonempty_pt_of_isBelyi (X : Curve) {φ : X.K} (hφ : IsBelyi φ)
    (hD : (X.D : Set (Place X.K)) = belyiCusps φ) : Nonempty X.Pt := by
  have htr : Transcendental ℚ (φ - 1 - 1) := by
    have := hφ.1.aeval (Polynomial.X - Polynomial.C 2) (by
      rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_X_sub_C]; exact one_mem _)
    convert this using 1
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_ofNat]
    ring
  obtain ⟨P, hP⟩ := Place.exists_notMem (transcendental_inv_iff.mpr htr)
  obtain ⟨x, rfl⟩ := QbarPoint.exists_P_eq P
  have hneg : x.P.ord (φ - 1 - 1)⁻¹ < 0 := (x.P.ord_neg_iff).mpr hP
  rw [Place.ord_inv] at hneg
  have hg0 : φ - 1 - 1 ≠ 0 := ne_zero_of_transcendental htr
  have hgm : φ - 1 - 1 ∈ x.P.1 := x.P.mem_of_ord_nonneg (by omega)
  have hφm : φ ∈ x.P.1 := by
    have : φ = (φ - 1 - 1) + 1 + 1 := by ring
    rw [this]
    exact add_mem (add_mem hgm x.P.1.one_mem) x.P.1.one_mem
  have hval : x.eval (φ - 1 - 1) hgm = 0 := (x.eval_eq_zero_iff hgm hg0).mpr (by omega)
  have hval' : x.eval φ hφm = 2 := by
    have h1 := x.eval_sub (sub_mem hφm x.P.1.one_mem) x.P.1.one_mem
    have h2 := x.eval_sub hφm x.P.1.one_mem
    rw [x.eval_one] at h1 h2
    rw [x.eval_congr rfl, h1, h2] at hval
    linear_combination hval
  have h2 : (2 : Qbar) ≠ 0 := two_ne_zero
  have h2' : (2 : Qbar) ≠ 1 := by norm_num
  refine ⟨⟨x, fun hx => ?_⟩⟩
  have hx' : x.P ∈ (X.D : Set (Place X.K)) := hx
  rw [hD] at hx'
  exact notMem_belyiCusps_of_eval x hφm (by rw [hval']; exact h2) (by rw [hval']; exact h2') hx'

set_option maxHeartbeats 800000 in
-- The construction of the covering and the Riemann–Hurwitz estimate below elaborate in one
-- proof, which exceeds the default heartbeat limit.
open Classical in
/-- **The first paragraph of the proof of [GenEll], Theorem 2.1** for the height theory of
curves over number fields: coverings ramified over the divisor. -/
theorem nonempty_covering (X : Curve) (hX : theory.Hyperbolic X) (d : ℕ) (ε' : ℝ)
    (hε' : 0 < ε') : Nonempty (theory.Covering X d ε') := by
  rcases X.cusp with hD | ⟨φ, hφ, hDφ⟩
  · exact ⟨coveringOfDivisorFree X hX hD d ε' hε'⟩
  change 0 < X.logCanon.deg at hX
  have hmemD : ∀ P : Place X.K, P ∈ X.D ↔ P.IsCuspOf φ := fun P => by
    rw [← Finset.mem_coe, hDφ]
    rfl
  have hDne : X.D.Nonempty := by
    obtain ⟨P, hP⟩ := Place.exists_notMem hφ.1
    exact ⟨P, (hmemD P).mpr (Or.inl ((P.ord_neg_iff).mpr hP).ne)⟩
  -- the numerical choices
  set h : ℝ := (X.logCanon.deg : ℝ) with hh
  set δ : ℝ := (X.divD.deg : ℝ) with hδ
  have hhpos : 0 < h := by rw [hh]; exact_mod_cast hX
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact_mod_cast deg_nonneg (divD_nonneg X)
  set e : ℕ := ⌈(1 + ε') * δ / (ε' * h)⌉₊ + 1 with he
  have hkey : (1 + ε') * δ < ε' * e * h := by
    have h1 : (1 + ε') * δ / (ε' * h) < e := by
      rw [he]
      push_cast
      linarith [Nat.le_ceil ((1 + ε') * δ / (ε' * h))]
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  have he1 : (1 : ℝ) ≤ e := by
    rw [he]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈(1 + ε') * δ / (ε' * h)⌉₊]
  set M : ℕ := ∑ P ∈ X.D, ((P.ord φ).natAbs + (P.ord (φ - 1)).natAbs) + 1 with hM
  have hMle : ∀ P ∈ X.D, |P.ord φ| < M ∧ |P.ord (φ - 1)| < M := by
    intro P hP
    have h1 : (P.ord φ).natAbs + (P.ord (φ - 1)).natAbs ≤
        ∑ Q ∈ X.D, ((Q.ord φ).natAbs + (Q.ord (φ - 1)).natAbs) :=
      Finset.single_le_sum (f := fun Q => (Q.ord φ).natAbs + (Q.ord (φ - 1)).natAbs)
        (fun _ _ => Nat.zero_le _) hP
    have h2 : (P.ord φ).natAbs < M := by omega
    have h3 : (P.ord (φ - 1)).natAbs < M := by omega
    constructor
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h2
    · rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  set N : ℕ := e * M with hNdef
  have hN : 0 < N :=
    Nat.mul_pos (by rw [he]; exact Nat.succ_pos _) (by rw [hM]; exact Nat.succ_pos _)
  -- the covering
  set Y := fermatCurve X φ hN with hY
  have hu := fermatU'_pow X φ hN
  have hv := fermatV'_pow X φ hN
  have hgen := adjoin_fermat_eq_top X φ hN
  -- ramification over the cusps
  have hram : ∀ Q : Place Y.K, X.divD (Q.restrict X.K) ≠ 0 → e ≤ Q.ramificationIdx X.K := by
    intro Q hQ
    have hQD : Q.restrict X.K ∈ X.D := by
      by_contra hc
      rw [divD_apply, if_neg hc] at hQ
      exact hQ rfl
    obtain ⟨hM1, hM2⟩ := hMle _ hQD
    have hepos : (0 : ℤ) < Q.ramificationIdx X.K := by exact_mod_cast Q.ramificationIdx_pos
    have hMpos : (0 : ℤ) < M := by rw [hM]; positivity
    have key : (N : ℤ) ≤ Q.ramificationIdx X.K * M := by
      rcases (hmemD _).mp hQD with hc | hc
      · have := Place.le_ramificationIdx_mul_abs_ord hu Q hc
        nlinarith
      · have := Place.le_ramificationIdx_mul_ord_sub_one hv Q hc
        have habs : (Q.restrict X.K).ord (φ - 1) = |(Q.restrict X.K).ord (φ - 1)| :=
          (abs_of_pos hc).symm
        nlinarith
    have : (e : ℤ) * M ≤ Q.ramificationIdx X.K * M :=
      calc (e : ℤ) * M = (N : ℤ) := by rw [hNdef]; push_cast; ring
        _ ≤ _ := key
    exact_mod_cast le_of_mul_le_mul_right this hMpos
  -- degrees
  set n : ℕ := finrank X.K Y.K with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; exact_mod_cast finrank_fermat_pos X φ hN
  have hdivY : Y.divD = 0 := by
    change ∑ P ∈ (∅ : Finset (Place Y.K)), Finsupp.single P 1 = 0
    rw [Finset.sum_empty]
  have hdegY : Y.logCanon.deg = n * X.canon.deg + (relRamDiv X.K Y.K).deg := by
    rw [Curve.logCanon, hdivY, add_zero, Curve.canon,
      deg_canonicalDiv_eq Y.sep_transcendental (transcendental_algebraMap X.sep_transcendental),
      canonicalDiv_algebraMap X.sep_transcendental, deg_add, deg_pullback]
    rfl
  have hdegpb : (pullback Y.K X.logCanon).deg = n * X.logCanon.deg := deg_pullback _
  have hR := sub_one_mul_deg_pullback_le (L := Y.K) X.divD (divD_nonneg X) (divD_le_one X) e hram
  rw [deg_pullback] at hR
  have hhk : h = X.canon.deg + δ := by
    rw [hh, hδ, Curve.logCanon, deg_add]; push_cast; ring
  have hR' : ((e : ℝ) - 1) * (n * δ) ≤ e * (relRamDiv X.K Y.K).deg := by
    rw [hδ]; exact_mod_cast hR
  have hYR : (Y.logCanon.deg : ℝ) = n * X.canon.deg + (relRamDiv X.K Y.K).deg := by
    rw [hdegY]; push_cast; ring
  set k : ℝ := (X.canon.deg : ℝ) with hk
  set R : ℝ := ((relRamDiv X.K Y.K).deg : ℝ) with hRdef
  have heh : 0 < (e : ℝ) * h := mul_pos (by linarith) hhpos
  have h2 : δ < e * h := by
    by_contra hc
    push Not at hc
    have : (1 + ε') * (e * h) ≤ (1 + ε') * δ := mul_le_mul_of_nonneg_left hc (by linarith)
    nlinarith
  have hYpos : 0 < Y.logCanon.deg := by
    have A : (e : ℝ) * (n * k + R) - n * (e * h - δ) = e * R - (e - 1) * (n * δ) := by
      rw [hhk]; ring
    have B : 0 < (n : ℝ) * (e * h - δ) := mul_pos hnpos (by linarith)
    have h1 : (0 : ℝ) < e * Y.logCanon.deg := by
      rw [hYR]
      linarith
    have h3 : (0 : ℝ) < Y.logCanon.deg := pos_of_mul_pos_right h1 (by positivity)
    exact_mod_cast h3
  have hdeg : ((pullback Y.K X.logCanon).deg : ℝ) < (1 + ε') * Y.logCanon.deg := by
    rw [hdegpb, hYR]
    push_cast
    rw [← hh]
    have A : (e : ℝ) * ((1 + ε') * (n * k + R) - n * h) - n * (ε' * e * h - (1 + ε') * δ) =
        (1 + ε') * (e * R - (e - 1) * (n * δ)) := by
      rw [hhk]; ring
    have B : 0 ≤ (1 + ε') * (e * R - (e - 1) * (n * δ)) :=
      mul_nonneg (by linarith) (by linarith)
    have C : 0 < (n : ℝ) * (ε' * e * h - (1 + ε') * δ) := mul_pos hnpos (by linarith)
    have D : 0 < (e : ℝ) * ((1 + ε') * (n * k + R) - n * h) := by linarith
    have E := pos_of_mul_pos_right D (by positivity)
    linarith
  -- a point of `X ∖ D` and the map on points
  obtain ⟨x₀⟩ := nonempty_pt_of_isBelyi X hφ hDφ
  let π : Y.Pt → X.Pt := fun y =>
    if hy : (y.1.restrict X.K).P ∈ X.D then x₀ else ⟨y.1.restrict X.K, hy⟩
  have hπ : ∀ (y : Y.Pt) (hy : (y.1.restrict X.K).P ∉ X.D), π y = ⟨y.1.restrict X.K, hy⟩ :=
    fun y hy => dif_neg hy
  have hπ₀ : ∀ (y : Y.Pt), (y.1.restrict X.K).P ∈ X.D → π y = x₀ := fun y hy => dif_pos hy
  -- the finitely many points over `D`
  set S : Set Y.Pt := {y | (y.1.restrict X.K).P ∈ X.D} with hS
  have hSfin : S.Finite := by
    have hT : {Q : Place Y.K | Q.restrict X.K ∈ X.D}.Finite := by
      have : {Q : Place Y.K | Q.restrict X.K ∈ X.D} = ⋃ P ∈ X.D, {Q | Q.restrict X.K = P} := by
        ext Q; simp
      rw [this]
      exact Set.Finite.biUnion X.D.finite_toSet fun P _ =>
        Place.finite_setOf_restrict_eq X.K (L := Y.K) P
    exact ((QbarPoint.finite_setOf_mem hT).preimage Subtype.val_injective.injOn).subset
      fun y hy => hy
  -- regularity of the model and of `φ, φ⁻¹, (1 - φ)⁻¹` off `D`
  set G' : Finset X.K := {φ, φ⁻¹, (1 - φ)⁻¹} with hG'
  have hG'reg : ∀ P : Place X.K, P ∉ X.D → ∀ g ∈ G', g ∈ P.1 := by
    intro P hP g hg
    obtain ⟨h1, h2, h3⟩ := mem_of_notMem_belyiCusps (φ := φ) (P := P) fun h => hP (by
      rw [← Finset.mem_coe, hDφ]; exact h)
    simp only [hG', Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hGreg : ∀ P : Place X.K, P ∉ X.D → ∀ g ∈ X.G, g ∈ P.1 := by
    intro P hP g hg
    have : g ∈ coordRing X.D := by
      rw [← X.G_spec hDne]
      exact Algebra.subset_adjoin hg
    exact this P hP
  obtain ⟨Cm, hCm⟩ := logCondOf_le_logCondOf_add X.G G' fun g hg => by
    rw [X.G_spec hDne]
    exact fun P hP => hG'reg P hP g hg
  -- Proposition 1.7 (i) off `D`
  have hmain : ∀ (y : Y.Pt), (y.1.restrict X.K).P ∉ X.D →
      logDiff y.1 ≤ logDiff (y.1.restrict X.K) + logCondOf X.G (y.1.restrict X.K) +
        (Cm + Heights.Different.kummerConst N) := by
    intro y hy
    have hyc : ¬ (y.1.restrict X.K).P.IsCuspOf φ := fun h => hy ((hmemD _).mpr h)
    set x := y.1.restrict X.K with hx
    have hφx : φ ∈ x.P.1 := QbarPoint.mem_φ _ hyc
    have hGx : ∀ g ∈ G', g ∈ x.P.1 := hG'reg _ hy
    have hGGx : ∀ g ∈ X.G, g ∈ x.P.1 := hGreg _ hy
    obtain ⟨ho1, ho2⟩ := Place.ord_eq_zero_of_not_isCuspOf hyc
    have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ.1
    have h1φ : 1 - φ ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      exact hφ.1 (h0 ▸ isAlgebraic_one)
    have hm1 : 1 - φ ∈ x.P.1 := sub_mem x.P.1.one_mem hφx
    have hz0 : x.eval φ hφx ≠ 0 := fun h0 => by
      have := (x.eval_eq_zero_iff hφx hφ0).mp h0
      omega
    have hz1 : x.eval φ hφx ≠ 1 := fun h0 => by
      have h2 : x.eval (1 - φ) hm1 = 0 := by
        rw [x.eval_sub x.P.1.one_mem hφx, x.eval_one, h0, sub_self]
      have := (x.eval_eq_zero_iff hm1 h1φ).mp h2
      omega
    set c : x.fieldOf := evalF x ⟨φ, hφx⟩ with hc
    have hc0 : c ≠ 0 := fun h0 => hz0 (congrArg Subtype.val h0)
    have hc1 : c ≠ 1 := fun h0 => hz1 (congrArg Subtype.val h0)
    have hcond := logCondOf_eq_cond G' x hGx
    have hK : Heights.Different.logDisc y.1.fieldOf ≤ Heights.Different.logDisc x.fieldOf +
        logCondOf G' x + Heights.Different.kummerConst N := by
      rw [hcond]
      refine logDisc_le_of_eq_adjoin (F := x.fieldOf) (L := y.1.fieldOf)
        (y.1.fieldOf_restrict_le (K := X.K)) hN (c := c)
        (QbarPoint.eval_u_pow hN hu y.1 hyc) (QbarPoint.eval_v_pow hN hv y.1 hyc)
        (QbarPoint.fieldOf_eq_adjoin_kummer hN hu hv hgen y.1 hyc) _
        (fun w hw => apply_eq_one_of_notMem_meets hc0 hc1 _ ⟨?_, ?_, ?_⟩ w hw)
      · simp only [Finset.mem_image, Finset.mem_attach, true_and]
        exact ⟨⟨φ, by simp [hG']⟩, rfl⟩
      · simp only [Finset.mem_image, Finset.mem_attach, true_and]
        refine ⟨⟨φ⁻¹, by simp [hG']⟩, Subtype.ext ?_⟩
        change x.eval φ⁻¹ _ = ((c⁻¹ : x.fieldOf) : Qbar)
        rw [x.eval_inv hφx, IntermediateField.coe_inv]
        rfl
      · simp only [Finset.mem_image, Finset.mem_attach, true_and]
        refine ⟨⟨(1 - φ)⁻¹, by simp [hG']⟩, Subtype.ext ?_⟩
        change x.eval (1 - φ)⁻¹ _ = (((1 - c)⁻¹ : x.fieldOf) : Qbar)
        rw [x.eval_inv hm1, IntermediateField.coe_inv, x.eval_sub x.P.1.one_mem hφx, x.eval_one]
        rfl
    have hm := hCm x hGGx hGx
    change Heights.Different.logDisc y.1.fieldOf ≤ Heights.Different.logDisc x.fieldOf +
      logCondOf X.G x + (Cm + Heights.Different.kummerConst N)
    linarith
  obtain ⟨B, hB⟩ := (hSfin.image fun y => logDiff y.1 - (logDiff (π y).1 +
    logCondOf X.G (π y).1)).bddAbove
  -- heights
  obtain ⟨Cp, hCp⟩ := divHeight_pullback (L := Y.K) X.logCanon
  obtain ⟨Cq, hCq⟩ := divHeight_le_mul (A := pullback Y.K X.logCanon) hYpos hdeg
  obtain ⟨Cb, hCb⟩ := divHeight_bddBelow hYpos
  set c₀ : ℝ := divHeight X.logCanon x₀.1 with hc₀
  refine ⟨{
    Y := Y
    hyperbolic := hYpos
    divisorFree := rfl
    d' := n * d
    π := π
    surjOn := ?_
    logDiff_le := ⟨max (Cm + Heights.Different.kummerConst N) B, fun y _ => ?_⟩
    htCan_le := ⟨max (Cp + Cq) (c₀ + (1 + ε') * Cb), fun y _ => ?_⟩ }⟩
  · intro x hx
    obtain ⟨y, hy, hydeg⟩ := QbarPoint.exists_restrict_eq (L := Y.K) x.1
    have hy' : (y.restrict X.K).P ∉ X.D := by rw [hy]; exact x.2
    refine ⟨⟨y, Finset.notMem_empty _⟩, ?_, ?_⟩
    · change y.deg ≤ n * d
      calc y.deg ≤ n * x.1.deg := hydeg
        _ ≤ n * d := Nat.mul_le_mul_left _ hx
    · rw [hπ ⟨y, Finset.notMem_empty _⟩ hy']
      exact Subtype.ext hy
  · simp only [Pi.add_apply, Function.comp_apply, theory_logDiff,
      theory_logCond_of_nonempty X hDne]
    by_cases hy : (y.1.restrict X.K).P ∈ X.D
    · have := hB ⟨y, hy, rfl⟩
      linarith [le_max_right (Cm + Heights.Different.kummerConst N) B]
    · rw [hπ y hy]
      have := hmain y hy
      linarith [le_max_left (Cm + Heights.Different.kummerConst N) B]
  · simp only [Pi.smul_apply, Function.comp_apply, theory_htCan, smul_eq_mul]
    have hb := hCb y.1
    by_cases hy : (y.1.restrict X.K).P ∈ X.D
    · rw [hπ₀ y hy]
      have : -((1 + ε') * Cb) ≤ (1 + ε') * divHeight Y.logCanon y.1 := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left hb (by linarith)
      linarith [le_max_right (Cp + Cq) (c₀ + (1 + ε') * Cb)]
    · rw [hπ y hy]
      have h1 := hCp y.1
      rw [abs_le] at h1
      have h2 := hCq y.1
      change divHeight X.logCanon (y.1.restrict X.K) ≤ _
      linarith [le_max_left (Cp + Cq) (c₀ + (1 + ε') * Cb), h1.1, h1.2]

end Genl.Curves
