-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicIntegrands
import Mathlib.Tactic

/-! # Parabolic scaling of the literal weak-equation integrand -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- The original weak integrand against the transported test equals the rescaled
weak integrand times the inverse quadratic time factor. -/
theorem parabolic_weak_integrand_scaling {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    {φ : ℝ × (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : ℝ × (Fin N → ℝ)) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    let ψ := parabolicTestTransport G t₀ x₀ r hr φ;
    -(u (T z).1 (T z).2 * fderiv ℝ ψ (T z) (1, 0)) +
      (∑ i, ∑ j, a (T z).1 (T z).2 i j * g j (T z).1 (T z).2 *
        fderiv ℝ ψ (T z) (0, G.horizontalFields hq i (T z).2)) =
      (r ^ 2)⁻¹ *
        (-(u (T z).1 (T z).2 * fderiv ℝ φ z (1, 0)) +
          ∑ i, ∑ j, a (T z).1 (T z).2 i j * (r * g j (T z).1 (T z).2) *
            fderiv ℝ φ z (0, G.horizontalFields hq i z.2)) := by
  dsimp only
  rw [fderiv_parabolicTestTransport_time_at_image G t₀ x₀ r hr hφ]
  simp_rw [fderiv_parabolicTestTransport_horizontal_at_image G hq hw t₀ x₀ r hr hφ]
  have hscale : r⁻¹ = (r ^ 2)⁻¹ * r := by field_simp
  simp_rw [hscale]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end HeatKernel
