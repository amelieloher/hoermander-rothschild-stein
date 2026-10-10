-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactSpacetimeDifferentiation

/-! # Smooth compact tests as differentiable L² curves

The differential in the time direction is the scalar time derivative.
For smooth compact tests it is continuous and compactly supported, so
it also differentiates the curve of L² spatial slices.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- The time differential of a smooth spacetime function is continuous. -/
theorem continuous_spacetime_time_differential {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (fun z => fderiv ℝ φ z (1, 0)) := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ φ) Set.univ :=
    hφ.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)
  exact (contDiffOn_univ.mp hf).continuous.clm_apply continuous_const

/-- The time differential is the scalar derivative of each fixed spatial slice. -/
theorem hasDerivAt_spacetime_time_slice {n : ℕ}
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun s => φ (s, x)) (fderiv ℝ φ (t, x) (1, 0)) t := by
  exact ((hφ.differentiable (by simp) (t, x)).hasFDerivAt).comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

end HeatKernel
