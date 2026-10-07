-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedFieldHomogeneity
public import RothschildStein.H1.ShellScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The complementary-degree kernel pairing with a
homogeneous field derivative of a cutoff is invariant under scaling. -/
theorem integral_homogeneous_field_cutoff_dilate
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k : ℝ}
    (hV : G2.IsHomogeneousField G V k) {f θ : (Fin N → ℝ) → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) {t : ℝ} (ht : 0 < t) :
    (∫ x, f x * fieldDerivative V (θ ∘ G.dilate t) x) =
      ∫ x, f x * fieldDerivative V θ x := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  have he : (fun x => f x * fieldDerivative V (θ ∘ G.dilate t) x) =ᵐ[volume]
      fun x => (t ^ G.homogeneousDimension) *
        (f (G.dilate t x) * fieldDerivative V θ (G.dilate t x)) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    rw [fieldDerivative_comp_dilate_at G hV ht x
      ((hθ.differentiable (by simp)).differentiableAt), hf t ht x hx]
    have hp : (t ^ G.homogeneousDimension : ℝ) * t ^ (k - (G.homogeneousDimension : ℝ)) = t ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]
      congr 1
      ring
    rw [← hp]
    ring
  rw [integral_congr_ae he, integral_const_mul,
    G2.integral_dilate G ht (fun x => f x * fieldDerivative V θ x)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos ht _)), one_mul]

end RothschildStein.H1
