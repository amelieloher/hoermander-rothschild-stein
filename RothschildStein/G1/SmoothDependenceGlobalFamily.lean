-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceGlobalBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P] [LocallyCompactSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous coefficient family gives jointly continuous
linear solutions on any prescribed bounded interval. There is no smallness
hypothesis on the interval (BB Proposition 1.2, p. 3). -/
theorem exists_continuous_linear_family_on_Icc
    {U : Set P} (hU : IsOpen U) {A : (P × ℝ) → E →L[ℝ] E}
    {T : ℝ} (hT : 0 < T) {K : ℝ≥0} (w₀ : E)
    (hA : ContinuousOn A (U ×ˢ Icc (-T) T))
    (hAb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖A (x, t)‖ ≤ K) :
    ∃ W : P → ℝ → E,
      ContinuousOn (fun p : P × ℝ => W p.1 p.2) (U ×ˢ Ioo (-T) T) ∧
      ∀ x ∈ U, Continuous (W x) ∧ W x 0 = w₀ ∧ ∀ t ∈ Icc (-T) T,
        ‖W x t‖ ≤ ‖w₀‖ * Real.exp ((K : ℝ) * T) ∧
        HasDerivAt (W x) (A (x, t) (W x t)) t := by
  classical
  have hex : ∀ x ∈ U, ∃ W : ℝ → E, Continuous W ∧ W 0 = w₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt W (A (x, t) (W t)) t := by
    intro x hx
    apply exists_linear_integralCurve_hasDerivAt_on_Icc hT.le (fun t => A (x, t))
      _ (hAb x hx) w₀
    exact hA.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hx, ht⟩)
  choose J hcJ hJ0 hJd using hex
  let W : P → ℝ → E := fun x => if hx : x ∈ U then J x hx else fun _ => 0
  have hwc : ∀ x ∈ U, Continuous (W x) := by
    intro x hx
    simpa only [W, dite_eq_left hx] using hcJ x hx
  have hw0 : ∀ x ∈ U, W x 0 = w₀ := by
    intro x hx
    simpa only [W, dite_eq_left hx] using hJ0 x hx
  have hwd : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, HasDerivAt (W x) (A (x, t) (W x t)) t := by
    intro x hx t ht
    simpa only [W, dite_eq_left hx] using hJd x hx t ht
  have hwb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖W x t‖ ≤ ‖w₀‖ * Real.exp ((K : ℝ) * T) := by
    intro x hx t ht
    simpa only [hw0 x hx] using linear_integralCurve_norm_bound hT.le (hAb x hx) (hwd x hx) t ht
  refine ⟨W, linear_solutions_continuousOn hU hT K.2 (by positivity) hA hAb
    (fun x hx t ht => (hwd x hx t ht).hasDerivWithinAt) hwb
    (fun x hx y hy => (hw0 x hx).trans (hw0 y hy).symm), ?_⟩
  exact fun x hx => ⟨hwc x hx, hw0 x hx, fun t ht => ⟨hwb x hx t ht, hwd x hx t ht⟩⟩

/-- Independent fundamental solutions exist jointly
continuously on an arbitrary bounded cylinder. They have ambient endpoint
derivatives and a uniform exponential bound (BB Proposition 1.2, p. 3). -/
theorem exists_continuous_fundamental_family_on_Icc
    {U : Set P} (hU : IsOpen U) {A : (P × ℝ) → E →L[ℝ] E}
    {T : ℝ} (hT : 0 < T) {K : ℝ≥0}
    (hA : ContinuousOn A (U ×ˢ Icc (-T) T))
    (hAb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖A (x, t)‖ ≤ K) :
    ∃ J : (P × ℝ) → E →L[ℝ] E,
      ContinuousOn J (U ×ˢ Ioo (-T) T) ∧
      ∀ x ∈ U, Continuous (fun t => J (x, t)) ∧
        J (x, 0) = ContinuousLinearMap.id ℝ E ∧
        ∀ t ∈ Icc (-T) T, ‖J (x, t)‖ ≤ Real.exp ((K : ℝ) * T) ∧
          HasDerivAt (fun s => J (x, s)) ((A (x, t)).comp (J (x, t))) t := by
  let B := fun p : P × ℝ => ContinuousLinearMap.compL ℝ E E E (A p)
  have hcB : ContinuousOn B (U ×ˢ Icc (-T) T) :=
    (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hA
  have hbB : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖B (x, t)‖ ≤ K := by
    intro x hx t ht
    calc
      ‖B (x, t)‖ ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖A (x, t)‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm _
      _ ≤ 1 * (K : ℝ) := mul_le_mul (ContinuousLinearMap.norm_compL_le ..)
        (hAb x hx t ht) (norm_nonneg _) (by norm_num)
      _ = K := one_mul _
  obtain ⟨J, hcJ, hJ⟩ := exists_continuous_linear_family_on_Icc hU hT
    (ContinuousLinearMap.id ℝ E) hcB hbB
  refine ⟨fun p => J p.1 p.2, hcJ, fun x hx => ⟨(hJ x hx).1, (hJ x hx).2.1, ?_⟩⟩
  intro t ht
  refine ⟨((hJ x hx).2.2 t ht).1.trans ?_, ?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) (Real.exp_pos _).le
  · simpa only [B, ContinuousLinearMap.compL_apply] using ((hJ x hx).2.2 t ht).2

end RothschildStein.G1
