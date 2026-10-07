-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KernelIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Explicit reciprocal-volume shell domination, BB (7.4), p. 297.
Closed inner endpoints are allowed, so this also controls endpoint error layers. -/
theorem DoublingPatch.lintegral_abs_le_shell (P : DoublingPatch X) {x : X} (hx : x ∈ P.S)
    {G : Set X} (hG : MeasurableSet G) {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbρ : b ≤ 6 * P.ρ) (hC : 0 ≤ C) {g : X → ℝ}
    (hsupp : ∀ y ∈ G, dist x y < a ∨ b ≤ dist x y → g y = 0)
    (hb : ∀ᵐ y ∂P.μ.restrict G, a ≤ dist x y → |g y| ≤ C * kernelWeight P.μ 0 x y) :
    (∫⁻ y in G, ENNReal.ofReal |g y| ∂P.μ) ≤
      ENNReal.ofReal (C * P.C_D * (b / a) ^ Real.logb 2 P.C_D) := by
  classical
  let V : Set X := {y | a ≤ dist x y ∧ dist x y < b}
  have hV : MeasurableSet V :=
    (measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable).inter
      (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const)
  have hdom : ∀ᵐ y ∂P.μ, G.indicator (fun y => ENNReal.ofReal |g y|) y ≤
      V.indicator (fun y => ENNReal.ofReal C * (volumeAt P.μ x y)⁻¹) y := by
    filter_upwards [(ae_restrict_iff' hG).mp hb] with y hby
    by_cases hy : y ∈ G
    swap
    · simp only [indicator_of_notMem hy, zero_le]
    by_cases hyV : y ∈ V
    swap
    · have hzero : g y = 0 := hsupp y hy (by
        dsimp [V] at hyV
        push Not at hyV
        by_cases hya : a ≤ dist x y
        · exact Or.inr (hyV hya)
        · exact Or.inl (lt_of_not_ge hya))
      simp only [indicator_of_mem hy, hzero, abs_zero, ENNReal.ofReal_zero, zero_le]
    rw [indicator_of_mem hy, indicator_of_mem hyV]
    have hv := P.doubling x hx (dist x y) (ha.trans_le hyV.1) (hyV.2.le.trans hbρ)
    have he := ENNReal.ofReal_le_ofReal (hby hy hyV.1)
    rw [ENNReal.ofReal_mul hC, ofReal_kernelWeight hv.1.ne' hv.2.1.ne] at he
    simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using he
  calc
    _ = ∫⁻ y, G.indicator (fun y => ENNReal.ofReal |g y|) y ∂P.μ := (lintegral_indicator hG _).symm
    _ ≤ ∫⁻ y, V.indicator (fun y => ENNReal.ofReal C * (volumeAt P.μ x y)⁻¹) y ∂P.μ := lintegral_mono_ae hdom
    _ = ENNReal.ofReal C * ∫⁻ y in V, (volumeAt P.μ x y)⁻¹ ∂P.μ := by
      rw [lintegral_indicator hV, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (P.C_D * (b / a) ^ Real.logb 2 P.C_D) :=
      mul_le_mul_right (P.shell_integral_rpow hx ha hab hbρ) _
    _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring

end RothschildStein.H2
