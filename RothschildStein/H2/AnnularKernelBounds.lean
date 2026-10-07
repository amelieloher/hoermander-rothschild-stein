-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DyadicShellDomination
public import RothschildStein.H2.IntegralBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Kernel bounds transfer any reciprocal-volume annulus bound to a
measurable annular input piece. The two endpoint corrections for the annular estimate (BB p. 303). -/
theorem KernelClass.annular_indicator_bound {D : LocDoubling X} {G N : Set X}
    {β A S a b C : ℝ} {K : X → X → ℝ} (hK : KernelClass D.μ G β 0 A S K)
    {x : X} (hx : x ∈ G) (hxΩ : x ∈ D.Ω₁) (hN : MeasurableSet N)
    (ha : 0 < a) (hb : b ≤ 6 * D.κ)
    (hNa : ∀ y ∈ G ∩ N, a ≤ dist x y ∧ dist x y < b) (hC : 0 ≤ C)
    (hvol : (∫⁻ y in {y | a ≤ dist x y ∧ dist x y < b}, (volumeAt D.μ x y)⁻¹ ∂D.μ) ≤ ENNReal.ofReal C) :
    IntegrableOn (N.indicator (K x)) G D.μ ∧
      |∫ y in G, N.indicator (K x) y ∂D.μ| ≤ A * C := by
  classical
  let V : Set X := {y | a ≤ dist x y ∧ dist x y < b}
  have hV : MeasurableSet V :=
    (measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable).inter
      (measurableSet_lt (continuous_const.dist continuous_id).measurable measurable_const)
  have hdom : ∀ᵐ y ∂D.μ, G.indicator (fun y => ENNReal.ofReal |N.indicator (K x) y|) y ≤
      V.indicator (fun y => ENNReal.ofReal A * (volumeAt D.μ x y)⁻¹) y := by
    filter_upwards [] with y
    by_cases hy : y ∈ G
    swap
    · simp only [indicator_of_notMem hy, zero_le]
    by_cases hyN : y ∈ N
    swap
    · simp only [indicator_of_mem hy, indicator_of_notMem hyN, abs_zero, ENNReal.ofReal_zero, zero_le]
    have hyd := hNa y ⟨hy, hyN⟩
    have hv := D.outerPatch.doubling x hxΩ (dist x y) (ha.trans_le hyd.1) (hyd.2.le.trans hb)
    rw [indicator_of_mem hy, indicator_of_mem hyN, indicator_of_mem (show y ∈ V from hyd)]
    change 0 < volumeAt D.μ x y ∧ volumeAt D.μ x y < ⊤ ∧
      volumeAt D.μ x y ≤ ENNReal.ofReal D.C_D * D.μ (ball x (dist x y / 2)) at hv
    have he := ENNReal.ofReal_le_ofReal (hK.size x hx y hy (dist_pos.mp (ha.trans_le hyd.1)))
    rw [ENNReal.ofReal_mul hK.A_nonneg, ofReal_kernelWeight hv.1.ne' hv.2.1.ne] at he
    simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using he
  have hl : (∫⁻ y in G, ENNReal.ofReal |N.indicator (K x) y| ∂D.μ) ≤ ENNReal.ofReal (A * C) := by
    calc
      _ = ∫⁻ y, G.indicator (fun y => ENNReal.ofReal |N.indicator (K x) y|) y ∂D.μ := (lintegral_indicator hK.measurable_E _).symm
      _ ≤ ∫⁻ y, V.indicator (fun y => ENNReal.ofReal A * (volumeAt D.μ x y)⁻¹) y ∂D.μ := lintegral_mono_ae hdom
      _ = ENNReal.ofReal A * ∫⁻ y in V, (volumeAt D.μ x y)⁻¹ ∂D.μ := by
        rw [lintegral_indicator hV, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal C := mul_le_mul_right hvol _
      _ = _ := (ENNReal.ofReal_mul hK.A_nonneg).symm
  have hi := integrableOn_of_subtype_lintegral hK.measurable_E
    ((hK.measurable_slice hx).aestronglyMeasurable.indicator (hN.preimage measurable_subtype_coe))
    (hl.trans_lt ENNReal.ofReal_lt_top)
  exact ⟨hi, abs_integral_le_of_lintegral hi (mul_nonneg hK.A_nonneg hC) hl⟩

end RothschildStein.H2
