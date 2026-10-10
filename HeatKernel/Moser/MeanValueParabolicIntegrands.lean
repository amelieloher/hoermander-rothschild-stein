-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicTestDerivatives
import Mathlib.Tactic

/-! # Derivative transport at the image of parabolic group coordinates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein RothschildStein.G2
namespace HeatKernel

/-- Evaluating a transported time derivative at the coordinate image recovers the
original test derivative with its inverse quadratic factor. -/
theorem fderiv_parabolicTestTransport_time_at_image {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : ℝ × (Fin N → ℝ)) :
    fderiv ℝ (parabolicTestTransport G t₀ x₀ r hr φ)
      (parabolicGroupHomeomorph G t₀ x₀ r hr z) (1, 0) =
      (r ^ 2)⁻¹ * fderiv ℝ φ z (1, 0) := by
  let T := parabolicGroupHomeomorph G t₀ x₀ r hr
  have he : ((r ^ 2)⁻¹ * (-t₀ + (T z).1),
      G.dilate r⁻¹ (G.mul (G.inv x₀) (T z).2)) = z := T.symm_apply_apply z
  have h := fderiv_parabolicTestTransport_time G t₀ x₀ r hr hφ (T z).1 (T z).2
  rw [he] at h
  exact h

/-- The horizontal derivative at the coordinate image has the inverse spatial factor. -/
theorem fderiv_parabolicTestTransport_horizontal_at_image {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin q) (z : ℝ × (Fin N → ℝ)) :
    fderiv ℝ (parabolicTestTransport G t₀ x₀ r hr φ)
      (parabolicGroupHomeomorph G t₀ x₀ r hr z)
        (0, G.horizontalFields hq i (parabolicGroupHomeomorph G t₀ x₀ r hr z).2) =
      r⁻¹ * fderiv ℝ φ z (0, G.horizontalFields hq i z.2) := by
  let T := parabolicGroupHomeomorph G t₀ x₀ r hr
  have he : ((r ^ 2)⁻¹ * (-t₀ + (T z).1),
      G.dilate r⁻¹ (G.mul (G.inv x₀) (T z).2)) = z := T.symm_apply_apply z
  have hx : G.dilate r⁻¹ (G.mul (G.inv x₀) (T z).2) = z.2 := congrArg Prod.snd he
  have h := fderiv_parabolicTestTransport_horizontal G hq hw t₀ x₀ r hr hφ i (T z).1 (T z).2
  rw [he, hx] at h
  exact h

end HeatKernel
