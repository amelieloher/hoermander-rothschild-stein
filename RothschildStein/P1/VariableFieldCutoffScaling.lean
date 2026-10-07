-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeightedFieldCutoffScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- Exact dilation of the cutoff flux for a
variable endpoint family. Both endpoint parameters move with the
integration variable; no parameter freezing is performed in this identity. -/
theorem integral_variableFieldCutoff_dilate (G : HomogeneousGroup N)
    {Y : (Fin N → ℝ) → (Fin N → ℝ)} {w β : ℝ}
    (hY : G2.IsHomogeneousField G Y w)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hΨ : ∀ ξ η, ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate t u) = t ^ β * Ψ ξ η u)
    (p : (Fin N → ℝ) → (Fin N → ℝ) × (Fin N → ℝ))
    {θ φ : (Fin N → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ u, Ψ (p u).1 (p u).2 u * fieldDerivative Y (θ ∘ G.dilate ε⁻¹) u * φ u) =
      ε ^ (β + (G.homogeneousDimension : ℝ) - w) *
        ∫ v, Ψ (p (G.dilate ε v)).1 (p (G.dilate ε v)).2 v *
          fieldDerivative Y θ v * φ (G.dilate ε v) := by
  let rsVariableCutoffFinNonempty : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  let a := fun u => Ψ (p u).1 (p u).2 u * fieldDerivative Y (θ ∘ G.dilate ε⁻¹) u * φ u
  have hscale : (∫ u, a u) = ε ^ G.homogeneousDimension * ∫ v, a (G.dilate ε v) := by
    rw [G2.integral_dilate G hε]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hε _)), one_mul]
  have he : (fun v => a (G.dilate ε v)) =ᵐ[volume]
      fun v => (ε ^ β * ε ^ (-w)) *
        (Ψ (p (G.dilate ε v)).1 (p (G.dilate ε v)).2 v *
          fieldDerivative Y θ v * φ (G.dilate ε v)) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with v hv
    dsimp only [a]
    rw [hΨ _ _ ε hε v hv,
      H1.fieldDerivative_comp_dilate_at G hY (inv_pos.mpr hε) (G.dilate ε v)
        ((hθ.differentiable (by simp)).differentiableAt),
      G2.dilate_inv_dilate G hε.ne', ← Real.rpow_neg_eq_inv_rpow]
    ring
  change (∫ u, a u) = _
  rw [hscale, integral_congr_ae he, integral_const_mul, ← mul_assoc,
    ← Real.rpow_natCast, ← Real.rpow_add hε, ← Real.rpow_add hε]
  congr 2
  ring

end RothschildStein.P1
