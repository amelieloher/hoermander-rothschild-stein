-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueParabolicCoordinates
import Mathlib.Tactic

/-! # Integration in parabolic group coordinates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory RothschildStein
namespace HeatKernel

/-- Composition with the parabolic coordinate map preserves integrability. -/
theorem integrable_comp_parabolicGroupHomeomorph {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {f : ℝ × (Fin N → ℝ) → ℝ} (hf : Integrable f) :
    Integrable (f ∘ parabolicGroupHomeomorph G t₀ x₀ r hr) := by
  apply (parabolicGroupHomeomorph G t₀ x₀ r hr).measurableEmbedding.integrable_map_iff.mp
  rw [map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- The Bochner integral in parabolic coordinates has the inverse spacetime Jacobian. -/
theorem integral_comp_parabolicGroupHomeomorph {N : ℕ} (G : HomogeneousGroup N)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (f : ℝ × (Fin N → ℝ) → ℝ) :
    (∫ z, f (parabolicGroupHomeomorph G t₀ x₀ r hr z)) =
      (r ^ (G.homogeneousDimension + 2))⁻¹ * ∫ z, f z := by
  rw [← (parabolicGroupHomeomorph G t₀ x₀ r hr).measurableEmbedding.integral_map f,
    map_parabolicGroupHomeomorph_volume G t₀ x₀ r hr, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _))]
  rfl

end HeatKernel
