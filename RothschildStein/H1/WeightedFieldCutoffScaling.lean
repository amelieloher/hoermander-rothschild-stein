-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FieldCutoffScaling
public import RothschildStein.G2.HomogeneousType

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: the cutoff-derivative term has its exact
scaling factor ε^(β+Q−k), with the test transported by Dε. -/
theorem integral_weightedFieldCutoff_dilate
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k β : ℝ}
    (hV : G2.IsHomogeneousField G V k) {f θ φ : (Fin N → ℝ) → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, f x * fieldDerivative V (θ ∘ G.dilate ε⁻¹) x * φ x) =
      ε ^ (β + (G.homogeneousDimension : ℝ) - k) *
        ∫ v, f v * fieldDerivative V θ v * φ (G.dilate ε v) := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  let a := fun x => f x * fieldDerivative V (θ ∘ G.dilate ε⁻¹) x * φ x
  have hscale : (∫ x, a x) = ε ^ G.homogeneousDimension * ∫ v, a (G.dilate ε v) := by
    rw [G2.integral_dilate G hε]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hε _)), one_mul]
  have he : (fun v => a (G.dilate ε v)) =ᵐ[volume]
      fun v => (ε ^ β * ε ^ (-k)) * (f v * fieldDerivative V θ v * φ (G.dilate ε v)) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with v hv
    dsimp only [a]
    rw [hf ε hε v hv,
      fieldDerivative_comp_dilate_at G hV (inv_pos.mpr hε) (G.dilate ε v)
        ((hθ.differentiable (by simp)).differentiableAt),
      G2.dilate_inv_dilate G hε.ne', ← Real.rpow_neg_eq_inv_rpow]
    ring
  change (∫ x, a x) = _
  rw [hscale, integral_congr_ae he, integral_const_mul, ← mul_assoc,
    ← Real.rpow_natCast, ← Real.rpow_add hε, ← Real.rpow_add hε]
  congr 2
  ring

end RothschildStein.H1
