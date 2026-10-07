-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Base

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate ComplexInnerProductSpace
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

theorem lambdaOperator_comp_apply (s t : ℝ) (u : TestFunction N) :
    lambdaOperator s (lambdaOperator t u) = lambdaOperator (s + t) u := by
  have := LinearMap.congr_fun (lambdaOperator_comp (N := N) s t) u
  exact this

theorem sobolevNorm_neg_half_sq (w : TestFunction N) :
    sobolevNorm (-1 / 2) w ^ 2 = (hermitianPairing (lambdaOperator (-1) w) w).re := by
  have h1 : sobolevNorm (-1 / 2) w = sobolevNorm 0 (lambdaOperator (-1 / 2) w) := by
    rw [sobolevNorm_eq_schwartzSobolevNorm, sobolevNorm_eq_schwartzSobolevNorm]
    have h := Hormander.A.Lambda_sobolevNorm (-1 / 2) 0 w
    rw [add_zero] at h
    exact h.symm
  rw [h1, sobolevNorm_zero_sq]
  have hp := Hormander.A.Lambda_pairing (N := N) (-1 / 2) w (lambdaOperator (-1) w)
  have e1 : (Hormander.A.Lambda (-(-1 / 2)) (lambdaOperator (-1) w) : TestFunction N) =
      lambdaOperator (-1 / 2) w := by
    change lambdaOperator (-(-1 / 2)) (lambdaOperator (-1) w) = _
    rw [lambdaOperator_comp_apply]; norm_num
  rw [e1] at hp
  have hp' : hermitianPairing (lambdaOperator (-1 / 2) w) (lambdaOperator (-1 / 2) w) =
      hermitianPairing (lambdaOperator (-1) w) w := by
    unfold hermitianPairing
    have e2 : ∀ (a b : Carrier N → ℂ), ∫ x, ⟪a x, b x⟫ = ∫ x, b x * conj (a x) := fun a b => by
      congr 1
    have hp2 := hp
    rw [e2 _ _, e2 _ _] at hp2
    exact hp2
  have := congrArg Complex.re hp'
  rw [H_self] at this
  simpa using this


theorem H_sub_left (u v w : TestFunction N) :
    hermitianPairing (u - v) w = hermitianPairing u w - hermitianPairing v w := by
  have := H_add_left (u - v) v w
  rw [sub_add_cancel] at this
  rw [this]; ring

theorem order0_bound {T : Operator N} (h : HasOrder 0 T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, sobolevNorm 0 (T u) ≤ C * sobolevNorm 0 u := by
  obtain ⟨C, hC⟩ := h 0
  exact ⟨C, C.2, fun u => by simpa using hC u⟩

/-- The pairing `H(V_i w, v)` after integration by parts. -/
theorem H_vectorField_left (Y : RealSchwartzVectorField N) (w v : TestFunction N) :
    hermitianPairing (vectorFieldOperator Y w) v =
      -hermitianPairing w (vectorFieldOperator Y v) +
        hermitianPairing w (realMultiplierOperator (negDiv Y) v) := by
  have := vectorField_hasHermitianAdjoint Y w v
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at this
  rw [this, H_add_right, H_neg_right]


theorem endpoint_pairing_expand {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (u v : TestFunction N) :
    hermitianPairing (vectorFieldOperator (X 0) u) v =
      hermitianPairing (diffusionOperator X c u) v -
        ∑ i : Fin k, hermitianPairing (vectorFieldOperator (X i.succ)
          (vectorFieldOperator (X i.succ) u)) v -
        hermitianPairing (realMultiplierOperator c u) v := by
  have hL : diffusionOperator X c u = (∑ i : Fin k, vectorFieldOperator (X i.succ)
      (vectorFieldOperator (X i.succ) u)) + vectorFieldOperator (X 0) u +
      realMultiplierOperator c u := by
    unfold diffusionOperator
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [hL, H_add_left, H_add_left, H_sum_left]
  ring

/-- The endpoint estimate:
`‖X₀ u‖²_{H^{-1/2}} ≤ C (‖Lu‖₂² + ‖u‖₂²)`. -/
theorem base_drift_endpoint_of_B10 (F : B10Facts N) {k : ℕ}
    (X : Fin (k + 1) → RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (-1 / 2) (vectorFieldOperator (X 0) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) + normSq u) := by
  set V0 := vectorFieldOperator (X 0) with hV0
  set Vop : Operator N := (lambdaOperator (-1)).comp V0 with hVop
  have hVc : OperatorClass 0 Vop := by
    have := F.comp_mem (-1) 1 _ _ (F.lambda_mem (-1)) (F.vectorField_mem (X 0))
    simpa using this
  obtain ⟨CV, hCV0, hCV⟩ := order0_bound hVc.hasOrder'
  have hcomm : ∀ i : Fin k, ∃ C : ℝ, 0 ≤ C ∧ ∀ u, sobolevNorm 0 (operatorComm
      (vectorFieldOperator (X i.succ)) Vop u) ≤ C * sobolevNorm 0 u := fun i =>
    order0_bound (F.comm_vectorField 0 Vop (X i.succ) hVc).hasOrder'
  have hgV : ∀ i : Fin k, ∃ C : ℝ, 0 ≤ C ∧ ∀ u, sobolevNorm 0
      (realMultiplierOperator (negDiv (X i.succ)) (Vop u)) ≤ C * sobolevNorm 0 u := fun i => by
    have := F.comp_mem 0 0 _ _ (F.multiplier_mem (negDiv (X i.succ))) hVc
    obtain ⟨C, hC0, hC⟩ := order0_bound (by simpa using this.hasOrder')
    exact ⟨C, hC0, fun u => hC u⟩
  choose C2 hC20 hC2 using hcomm
  choose C3 hC30 hC3 using hgV
  obtain ⟨Cm, hCm0, hCm⟩ := order0_bound (hasOrder_multiplierOperator_zero (complexifyRealSchwartz c))
  obtain ⟨C6, hC6, hE⟩ := energy_bound X c
  set D : ℝ := ∑ i : Fin k, (C2 i + C3 i) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => add_nonneg (hC20 i) (hC30 i)
  have hDi : ∀ i : Fin k, C2 i + C3 i ≤ D := fun i =>
    Finset.single_le_sum (f := fun i : Fin k => C2 i + C3 i)
      (fun j _ => add_nonneg (hC20 j) (hC30 j)) (Finset.mem_univ i)
  refine ⟨CV / 2 + (CV + D / 2) * C6 + D * k / 2 + Cm * CV + 1, by positivity, fun u => ?_⟩
  set v : TestFunction N := Vop u with hv
  set a := sobolevNorm 0 (diffusionOperator X c u) with ha
  set n := sobolevNorm 0 u with hn
  set e : Fin k → ℝ := fun i => sobolevNorm 0 (vectorFieldOperator (X i.succ) u) with he
  have ha0 : 0 ≤ a := sobolevNorm_nonneg _ _
  have hn0 : 0 ≤ n := sobolevNorm_nonneg _ _
  have he0 : ∀ i, 0 ≤ e i := fun i => sobolevNorm_nonneg _ _
  have s1 : sobolevNorm (-1 / 2) (V0 u) ^ 2 = (hermitianPairing (Vop u) (V0 u)).re :=
    sobolevNorm_neg_half_sq (V0 u)
  have s2 : (hermitianPairing (Vop u) (V0 u)).re ≤ ‖hermitianPairing (V0 u) v‖ := by
    rw [H_re_symm]; exact Complex.re_le_norm _
  have hexp := endpoint_pairing_expand X c u v
  have key : ∀ i : Fin k, ‖hermitianPairing (vectorFieldOperator (X i.succ)
      (vectorFieldOperator (X i.succ) u)) v‖ ≤ CV * e i ^ 2 + (C2 i + C3 i) * (e i * n) := by
    intro i
    have h1 := H_vectorField_left (X i.succ) (vectorFieldOperator (X i.succ) u) v
    have h2 : vectorFieldOperator (X i.succ) v = Vop (vectorFieldOperator (X i.succ) u) +
        operatorComm (vectorFieldOperator (X i.succ)) Vop u := by
      simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, hv]; abel
    rw [h2, H_add_right] at h1
    rw [h1]
    have b1 := norm_H_le (vectorFieldOperator (X i.succ) u)
      (Vop (vectorFieldOperator (X i.succ) u))
    have b2 := norm_H_le (vectorFieldOperator (X i.succ) u)
      (operatorComm (vectorFieldOperator (X i.succ)) Vop u)
    have b3 := norm_H_le (vectorFieldOperator (X i.succ) u)
      (realMultiplierOperator (negDiv (X i.succ)) v)
    have c1 := hCV (vectorFieldOperator (X i.succ) u)
    have c2 := hC2 i u
    have c3 := hC3 i u
    have ei0 := he0 i
    calc ‖-(hermitianPairing (vectorFieldOperator (X i.succ) u) (Vop (vectorFieldOperator (X i.succ) u)) +
          hermitianPairing (vectorFieldOperator (X i.succ) u)
            (operatorComm (vectorFieldOperator (X i.succ)) Vop u)) +
          hermitianPairing (vectorFieldOperator (X i.succ) u)
            (realMultiplierOperator (negDiv (X i.succ)) v)‖
        ≤ ‖hermitianPairing (vectorFieldOperator (X i.succ) u) (Vop (vectorFieldOperator (X i.succ) u))‖ +
          ‖hermitianPairing (vectorFieldOperator (X i.succ) u)
            (operatorComm (vectorFieldOperator (X i.succ)) Vop u)‖ +
          ‖hermitianPairing (vectorFieldOperator (X i.succ) u)
            (realMultiplierOperator (negDiv (X i.succ)) v)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_neg]
          gcongr
          exact norm_add_le _ _
      _ ≤ e i * (CV * e i) + e i * (C2 i * n) + e i * (C3 i * n) := by
          gcongr
          · exact b1.trans (mul_le_mul_of_nonneg_left c1 ei0)
          · exact b2.trans (mul_le_mul_of_nonneg_left c2 ei0)
          · exact b3.trans (mul_le_mul_of_nonneg_left c3 ei0)
      _ = _ := by ring
  have hsum : ‖hermitianPairing (V0 u) v‖ ≤ ‖hermitianPairing (diffusionOperator X c u) v‖ +
      ∑ i : Fin k, (CV * e i ^ 2 + (C2 i + C3 i) * (e i * n)) +
      ‖hermitianPairing (realMultiplierOperator c u) v‖ := by
    rw [hexp]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => key i
  have hvn : sobolevNorm 0 v ≤ CV * n := hCV u
  have bL : ‖hermitianPairing (diffusionOperator X c u) v‖ ≤ a * (CV * n) :=
    (norm_H_le _ _).trans (mul_le_mul_of_nonneg_left hvn ha0)
  have bM : ‖hermitianPairing (realMultiplierOperator c u) v‖ ≤ (Cm * n) * (CV * n) :=
    (norm_H_le _ _).trans (mul_le_mul (hCm u) hvn (sobolevNorm_nonneg _ _) (by positivity))
  have hE' : ∑ i : Fin k, e i ^ 2 ≤ C6 * (a ^ 2 + n ^ 2) := by
    have := hE u
    simp only [he, ha, hn, sobolevNorm_zero_sq]
    exact this
  have hen : ∑ i : Fin k, (e i * n) ≤ (1 / 2) * ∑ i : Fin k, e i ^ 2 + (k / 2) * n ^ 2 := by
    have : ∀ i : Fin k, e i * n ≤ (1 / 2) * e i ^ 2 + (1 / 2) * n ^ 2 := fun i => by
      nlinarith [sq_nonneg (e i - n)]
    calc ∑ i : Fin k, (e i * n) ≤ ∑ i : Fin k, ((1 / 2) * e i ^ 2 + (1 / 2) * n ^ 2) :=
          Finset.sum_le_sum fun i _ => this i
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp [Finset.sum_const]; ring
  have hsum2 : ∑ i : Fin k, (CV * e i ^ 2 + (C2 i + C3 i) * (e i * n)) ≤
      CV * ∑ i : Fin k, e i ^ 2 + D * ((1 / 2) * ∑ i : Fin k, e i ^ 2 + (k / 2) * n ^ 2) := by
    calc _ ≤ ∑ i : Fin k, (CV * e i ^ 2 + D * (e i * n)) :=
          Finset.sum_le_sum fun i _ => by
            have := mul_le_mul_of_nonneg_right (hDi i) (mul_nonneg (he0 i) hn0)
            linarith
      _ = CV * ∑ i : Fin k, e i ^ 2 + D * ∑ i : Fin k, (e i * n) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hen hD0
          linarith
  have hE0 : 0 ≤ ∑ i : Fin k, e i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgoal : sobolevNorm (-1 / 2) (V0 u) ^ 2 ≤
      (CV / 2 + (CV + D / 2) * C6 + D * k / 2 + Cm * CV + 1) * (a ^ 2 + n ^ 2) := by
    set E := ∑ i : Fin k, e i ^ 2 with hEdef
    have t1 : a * (CV * n) ≤ CV / 2 * (a ^ 2 + n ^ 2) := by
      nlinarith [sq_nonneg (a - n), mul_nonneg hCV0 (sq_nonneg (a - n))]
    have t2 : (Cm * n) * (CV * n) ≤ Cm * CV * (a ^ 2 + n ^ 2) := by
      have : 0 ≤ Cm * CV := mul_nonneg hCm0 hCV0
      nlinarith [mul_nonneg this (sq_nonneg a), mul_nonneg this (sq_nonneg n)]
    have t3 : (CV + D / 2) * E ≤ (CV + D / 2) * C6 * (a ^ 2 + n ^ 2) := by
      have := mul_le_mul_of_nonneg_left hE' (by positivity : 0 ≤ CV + D / 2)
      linarith
    have t4 : D * (k / 2) * n ^ 2 ≤ D * k / 2 * (a ^ 2 + n ^ 2) := by
      have : 0 ≤ D * k / 2 := by positivity
      nlinarith [mul_nonneg this (sq_nonneg a)]
    nlinarith [s1, s2, hsum, bL, bM, hsum2, t1, t2, t3, t4, sq_nonneg a, sq_nonneg n]
  simpa only [ha, hn, sobolevNorm_zero_sq] using hgoal

/-- for `0 < α ≤ 1/2`:
`‖X₀ u‖²_{H^{α-1}} ≤ C (‖Lu‖₂² + ‖u‖₂²)`. -/
theorem base_drift_of_B10 (F : B10Facts N) {k : ℕ}
    (X : Fin (k + 1) → RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ) {α : ℝ}
    (hα : α ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : TestFunction N,
      sobolevNorm (α - 1) (vectorFieldOperator (X 0) u) ^ 2 ≤
        C * (normSq (diffusionOperator X c u) + normSq u) := by
  obtain ⟨C, hC, h⟩ := base_drift_endpoint_of_B10 F X c
  refine ⟨C, hC, fun u => ?_⟩
  have h1 : sobolevNorm (α - 1) (vectorFieldOperator (X 0) u) ≤
      sobolevNorm (-1 / 2) (vectorFieldOperator (X 0) u) := sobolevNorm_mono (by linarith) _
  exact (pow_le_pow_left₀ (sobolevNorm_nonneg _ _) h1 2).trans (h u)

end Hormander.C
