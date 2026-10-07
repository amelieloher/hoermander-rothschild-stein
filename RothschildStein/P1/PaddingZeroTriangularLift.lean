-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldSmoothness
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.Definitions.triangularLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- The original fields in diffusion padding are exactly the
zero-polynomial triangular lift, allowing reuse of weak-word descent. -/
theorem paddingBaseFields_eq_zero_triangularLift {k n d : ℕ}
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)) :
    (fun i => paddingBaseField (d := d) (X i)) =
      triangularLift X (0 : Fin k → Fin d → MvPolynomial (Fin (n + d)) ℝ) := by
  ext i ξ j
  refine Fin.addCases ?_ ?_ j
  · intro l
    simp [paddingBaseField, triangularLift, joinPoint, paddingBaseCLM_apply]
  · intro l
    simp [paddingBaseField, triangularLift, joinPoint]

/-- Smoothness of the zero-polynomial triangular lift on the
actual product cylinder, using coefficients local to the base domain. -/
theorem contDiffOn_zero_triangularLift_cylinder {k n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (triangularLift X (0 : Fin k → Fin d → MvPolynomial (Fin (n + d)) ℝ) i)
      (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
  rw [← paddingBaseFields_eq_zero_triangularLift]
  intro i
  exact (contDiffOn_paddingBaseField (Ω : Set (Fin n → ℝ)) (X i) (hX i)).mono
    (by intro ξ hξ; exact padding_cylinder_subset_base Ω J hξ)

end RothschildStein.P1
