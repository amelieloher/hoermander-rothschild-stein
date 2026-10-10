-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.PositiveTimeKernelMeasures
public import HeatKernel.Kernel.DilationSubstitution

/-! # Weak delta convergence of conservative covariant kernel measures

Translation and parabolic dilation identify every kernel row with a rescaled
integrable unit-mass profile. The resulting bounded-test initial condition
is weak convergence of the row probability measures to their spatial center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter RothschildStein
open scoped Topology

namespace HeatKernel

/-- Conservative translation-invariant parabolically scaling kernel rows converge weakly to their point masses. -/
theorem tendsto_kernel_probabilityMeasures_of_covariance_and_unit_mass {n : ℕ}
    (G : HomogeneousGroup n) (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hp : ∀ t, 0 < t → ∀ x, Integrable (p t x) volume)
    (hnonneg : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hmass : ∀ t, 0 < t → ∀ x, (∫ y, p t x y) = 1)
    (hinv : ∀ t, 0 < t → ∀ g x y, p t (G.mul g x) (G.mul g y) = p t x y)
    (hscale : ∀ r t, 0 < r → 0 < t → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y) (x : Fin n → ℝ) :
    Tendsto (positiveTimeKernelProbabilityMeasure volume (fun t => p t x)
      (fun t ht => hp t ht x) (fun t ht => hnonneg t ht x)
      (fun t ht => hmass t ht x) x) (𝓝[>] 0)
      (𝓝 ((Measure.dirac x).toProbabilityMeasure)) := by
  apply tendsto_positiveTimeKernelProbabilityMeasure
  intro φ hφ hbounded
  obtain ⟨C, hC⟩ := hbounded
  exact tendsto_kernel_integral_of_covariance_and_unit_mass G p hinv hscale
    (hp 1 zero_lt_one 0) (hmass 1 zero_lt_one 0) hφ
    (by simpa only [Real.norm_eq_abs] using hC) x

end HeatKernel
