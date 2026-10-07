-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousTransposeConstant
public import RothschildStein.H1.ShellScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: the transpose pairing is unchanged by dilation
of the cutoff, for a function of the complementary degree k − Q
(BB Corollary 6.31, p. 280). -/
theorem integral_homogeneous_transpose_dilate
    (P : SmoothDifferentialOperator N) {k : ℝ} (hP : P.IsHomogeneous G k)
    {f : (Fin N → ℝ) → ℝ}
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    {θ : (Fin N → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    {t : ℝ} (ht : 0 < t) :
    (∫ x, f x * G2.differentialTranspose P (θ ∘ G.dilate t) x) =
      ∫ x, f x * G2.differentialTranspose P θ x := by
  have : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  have he : (fun x => f x * G2.differentialTranspose P (θ ∘ G.dilate t) x) =ᵐ[volume]
      fun x => (t ^ G.homogeneousDimension) *
        (f (G.dilate t x) * G2.differentialTranspose P θ (G.dilate t x)) := by
    filter_upwards [volume.ae_ne (0 : Fin N → ℝ)] with x hx
    rw [G2.differentialTranspose_homogeneous G P k hP θ hθ t ht x, hf t ht x hx]
    have hp : (t ^ G.homogeneousDimension : ℝ) * t ^ (k - (G.homogeneousDimension : ℝ)) = t ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ht]
      congr 1
      ring
    rw [← hp]
    ring
  rw [integral_congr_ae he, integral_const_mul,
    G2.integral_dilate G ht (fun x => f x * G2.differentialTranspose P θ x)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos ht _)), one_mul]

end RothschildStein.H1
