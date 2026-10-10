-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueUnitCylinderScaling
public import HeatKernel.Moser.MeanValueScaledMeasures
import Mathlib.Tactic

/-! # Exact domains and quadratic integrals under cylinder scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Parabolic coordinates map every backward time interval and centered horizontal
ball onto the exactly scaled cylinder. -/
theorem image_scaled_cylinder_parabolicGroupHomeomorph {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) (a ρ : ℝ) :
    parabolicGroupHomeomorph G t₀ x₀ r hr ''
      (Ioo (-a) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 ρ) =
        Ioo (t₀ - r ^ 2 * a) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ (r * ρ) := by
  have hball : (fun y => G.mul x₀ (G.dilate r y)) ''
      horizontalBall (G.horizontalFields hq) 0 ρ =
        horizontalBall (G.horizontalFields hq) x₀ (r * ρ) := by
    rw [← image_image, image_horizontalBall_dilate G hq hw hr,
      G2.dilate_zero, image_horizontalBall_leftTranslation, G2.mul_zero]
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [parabolicGroupHomeomorph_apply]
      constructor <;> nlinarith [mul_lt_mul_of_pos_left hy.1.1 (sq_pos_of_pos hr),
        mul_lt_mul_of_pos_left hy.1.2 (sq_pos_of_pos hr)]
    · rw [← hball]
      exact ⟨y.2, hy.2, rfl⟩
  · intro hz
    rw [← hball] at hz
    obtain ⟨y, hy, heq⟩ := hz.2
    refine ⟨((z.1 - t₀) / r ^ 2, y), ⟨?_, hy⟩, ?_⟩
    · constructor
      · apply (lt_div_iff₀ (sq_pos_of_pos hr)).mpr
        linarith [hz.1.1]
      · apply (div_lt_iff₀ (sq_pos_of_pos hr)).mpr
        linarith [hz.1.2]
    · apply Prod.ext
      · simp only [parabolicGroupHomeomorph_apply]
        field_simp
        ring
      · exact heq

/-- The unit backward cylinder has its expected image under parabolic coordinates. -/
theorem image_unit_cylinder_parabolicGroupHomeomorph {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    parabolicGroupHomeomorph G t₀ x₀ r hr ''
      (Ioo (-1 : ℝ) 0 ×ˢ horizontalBall (G.horizontalFields hq) 0 1) =
        Ioo (t₀ - r ^ 2) t₀ ×ˢ horizontalBall (G.horizontalFields hq) x₀ r := by
  simpa only [mul_one] using
    image_scaled_cylinder_parabolicGroupHomeomorph G hq hw t₀ x₀ r hr 1 1

/-- The ordinary real ball volume has the same exact homogeneous scaling. -/
theorem real_volume_horizontalBall {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r) :
    volume.real (horizontalBall (G.horizontalFields hq) x₀ r) =
      r ^ G.homogeneousDimension * volume.real (horizontalBall (G.horizontalFields hq) 0 1) := by
  simp only [Measure.real, volume_horizontalBall G hq hw x₀ hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

end HeatKernel
