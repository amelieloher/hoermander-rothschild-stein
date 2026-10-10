-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smoothing scalar contractions

Convolution with a nonnegative normalized bump preserves the Lipschitz constant of a scalar
contraction. Subtracting the value at zero preserves that constant and fixes zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Convolution Topology NNReal

namespace HeatKernel

/-- The normalized smooth average of a scalar function. -/
def smoothScalarAverage (φ : ContDiffBump (0 : ℝ)) (η : ℝ → ℝ) : ℝ → ℝ :=
  φ.normed volume ⋆ η

/-- A continuous scalar function becomes smooth after normalized bump convolution. -/
theorem contDiff_smoothScalarAverage (φ : ContDiffBump (0 : ℝ)) {η : ℝ → ℝ}
    (hη : Continuous η) : ContDiff ℝ (⊤ : ℕ∞) (smoothScalarAverage φ η) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hη.locallyIntegrable

/-- Normalized bump convolution preserves the Lipschitz constant one. -/
theorem lipschitzWith_smoothScalarAverage (φ : ContDiffBump (0 : ℝ)) {η : ℝ → ℝ}
    (hη : LipschitzWith 1 η) : LipschitzWith 1 (smoothScalarAverage φ η) := by
  have hint : ∀ x : ℝ, Integrable (fun t => φ.normed volume t * η (x - t)) := by
    intro x
    exact ((φ.contDiff_normed (n := ⊤)).continuous.mul
      (hη.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_right
  have hk : Integrable (φ.normed volume) :=
    (φ.contDiff_normed (n := ⊤)).continuous.integrable_of_hasCompactSupport φ.hasCompactSupport_normed
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  change dist (∫ t, φ.normed volume t * η (x - t))
    (∫ t, φ.normed volume t * η (y - t)) ≤ dist x y
  rw [dist_eq_norm, ← integral_sub (hint x) (hint y)]
  calc
    ‖∫ t, φ.normed volume t * η (x - t) - φ.normed volume t * η (y - t)‖
        ≤ ∫ t, ‖φ.normed volume t * η (x - t) - φ.normed volume t * η (y - t)‖ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ t, φ.normed volume t * dist x y := by
      apply integral_mono_ae ((hint x).sub (hint y)).norm (hk.mul_const (dist x y))
      apply Eventually.of_forall
      intro t
      simp only [Pi.sub_apply]
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [NNReal.coe_one, one_mul, ← dist_eq_norm, dist_sub_right] using
        hη.dist_le_mul (x - t) (y - t)
    _ = dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

end HeatKernel
