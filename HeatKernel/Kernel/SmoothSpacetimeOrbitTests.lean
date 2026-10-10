-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothSpacetimeDifferentiation

/-! # Smooth spacetime tests of Hilbert-space orbits

Smooth compact spacetime tests define differentiable L² curves with
compact time support. A generator pairing identity then gives their
integrated weak time identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace

namespace HeatKernel

/-- A smooth compact spacetime test gives the integrated weak orbit identity from a generator pairing. -/
theorem integral_inner_orbit_smooth_spacetime_test_eq_zero {n : ℕ}
    (I : Opens ℝ) (u ψ : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (I : Set ℝ) ×ˢ Set.univ)
    (hu : ContDiffOn ℝ 1 u (I : Set ℝ))
    (hpair : ∀ t, inner ℝ (deriv u t)
      ((memLp_two_spatial_slice φ hφ.continuous hc t).toLp (fun x => φ (t, x))) =
      inner ℝ (u t) (ψ t)) :
    Integrable (fun t => inner ℝ (u t)
      ((memLp_two_spatial_slice (fun z => fderiv ℝ φ z (1, 0))
        (continuous_spacetime_time_differential φ hφ)
        (hc.fderiv_apply (𝕜 := ℝ) (1, 0)) t).toLp
        (fun x => fderiv ℝ φ (t, x) (1, 0)) + ψ t)) ∧
      (∫ t, inner ℝ (u t)
        ((memLp_two_spatial_slice (fun z => fderiv ℝ φ z (1, 0))
          (continuous_spacetime_time_differential φ hφ)
          (hc.fderiv_apply (𝕜 := ℝ) (1, 0)) t).toLp
          (fun x => fderiv ℝ φ (t, x) (1, 0)) + ψ t)) = 0 := by
  apply integral_inner_orbit_scalar_time_test_eq_zero I u ψ
    (fun t x => φ (t, x)) (fun t x => fderiv ℝ φ (t, x) (1, 0))
    (memLp_two_spatial_slice φ hφ.continuous hc)
    (memLp_two_spatial_slice (fun z => fderiv ℝ φ z (1, 0))
      (continuous_spacetime_time_differential φ hφ) (hc.fderiv_apply (𝕜 := ℝ) (1, 0))) hu
  · exact hasDerivAt_toLp_spatial_slices φ (fun z => fderiv ℝ φ z (1, 0))
      hφ.continuous (continuous_spacetime_time_differential φ hφ) hc
      (hc.fderiv_apply (𝕜 := ℝ) (1, 0)) (hasDerivAt_spacetime_time_slice φ hφ)
  · exact continuous_toLp_spatial_slices (fun z => fderiv ℝ φ z (1, 0))
      (continuous_spacetime_time_differential φ hφ) (hc.fderiv_apply (𝕜 := ℝ) (1, 0))
  · exact hc.image continuous_fst
  · rintro t ⟨z, hz, rfl⟩
    exact (hs hz).1
  · intro t ht
    exact Filter.Eventually.of_forall fun x =>
      congrFun (spatial_slice_eq_zero_outside_time_projection φ ht) x
  · exact hpair

end HeatKernel
