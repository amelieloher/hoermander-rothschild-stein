-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZDecomposition

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

omit [Countable ι] in
/-- The good part has square integral bounded by its height times the original L¹ mass (BB pp. 319–320). -/
theorem CZDecompositionFacts.good_square_integral (μ : Measure X)
    {B : ι → Set X} {f g : X → ℝ} {b : ι → X → ℝ} {C : ℝ}
    (hcz : CZDecompositionFacts μ B f C g b) (hf : Integrable f μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rcases hcz with ⟨_, _, hgi, _, _, hgbound, hmass, _⟩
  have he : (∫⁻ x, ‖g x‖ₑ ∂μ) = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hgi,
      ← ofReal_integral_norm_eq_lintegral_enorm hf]
    congr 1
    calc
      _ = ∫ x, g x ∂μ := integral_congr_ae (hgbound.mono fun x hx => Real.norm_of_nonneg hx.1)
      _ = ∫ x, f x ∂μ := hmass
      _ = _ := integral_congr_ae (hn.mono fun x hx => (Real.norm_of_nonneg hx).symm)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal C * ‖g x‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hgbound] with x hx
      have hb : ‖g x‖ₑ ≤ ENNReal.ofReal C := by
        rw [← ofReal_norm, Real.norm_of_nonneg hx.1]
        exact ENNReal.ofReal_le_ofReal hx.2
      rw [pow_two]
      exact mul_le_mul' hb le_rfl
    _ = ENNReal.ofReal C * ∫⁻ x, ‖g x‖ₑ ∂μ :=
      lintegral_const_mul'' _ hgi.aemeasurable.enorm
    _ = _ := congrArg (fun t => ENNReal.ofReal C * t) he

end RothschildStein.H2
