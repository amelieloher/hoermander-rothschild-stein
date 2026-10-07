-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderModule

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The induced L² inner product is the integral of the representatives. -/
theorem holderL2_inner {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (f g : holderFunctions δ U) :
    inner ℝ (holderL2 δ U μ hδ hU hμ f) (holderL2 δ U μ hδ hU hμ g) =
      ∫ x in U, (f : X → ℝ) x * (g : X → ℝ) x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(f.property.1.memLp_two hδ hU hμ).coeFn_toLp,
    (g.property.1.memLp_two hδ hU hμ).coeFn_toLp] with x hx hy
  change inner ℝ ((f.property.1.memLp_two hδ hU hμ).toLp (f : X → ℝ) x)
    ((g.property.1.memLp_two hδ hU hμ).toLp (g : X → ℝ) x) = _
  rw [hx, hy]
  exact Real.inner_apply _ _

/-- Multiplication by a uniformly bounded coefficient on U is
bounded on the actual L² embedding, with its supremum bound. -/
theorem holderL2_mul_norm_le {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (f g : holderFunctions δ U) {h : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ U, |h x| ≤ C) (hg : EqOn (g : X → ℝ) (fun x => h x * (f : X → ℝ) x) U) :
    ‖holderL2 δ U μ hδ hU hμ g‖ ≤ C * ‖holderL2 δ U μ hδ hU hμ f‖ := by
  have hfLp := f.property.1.memLp_two hδ hU hμ
  have hgLp := g.property.1.memLp_two hδ hU hμ
  have hb : ∀ᵐ x ∂μ.restrict U, ‖(g : X → ℝ) x‖ ≤ C * ‖(f : X → ℝ) x‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [hg hx, Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound x hx) (abs_nonneg _)
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hgLp.aestronglyMeasurable hb (p := 2)
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfLp.eLpNorm_ne_top) he
  change ‖hgLp.toLp (g : X → ℝ)‖ ≤ C * ‖hfLp.toLp (f : X → ℝ)‖
  rw [Lp.norm_toLp, Lp.norm_toLp]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hr

end RothschildStein.H2
