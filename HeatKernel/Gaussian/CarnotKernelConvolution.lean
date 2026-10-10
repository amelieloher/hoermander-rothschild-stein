-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CarnotPoint
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Kernel convolution in Carnot coordinates

Coordinate Lebesgue convolution agrees with convolution for the volume measure
on the horizontal metric space.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel.Gaussian

/-- The coordinate Chapman–Kolmogorov equality transfers to Carnot volume with
the kernel value on the left. -/
theorem carnot_kernel_convolution_eq {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (h : ∀ s t, 0 < s → 0 < t → ∀ x y,
      ∫ z, p s x z * p t z y ∂volume = p (s + t) x y) :
    ∀ s t, 0 < s → 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan,
      p (s + t) x y = ∫ z, p s x z * p t z y ∂(CarnotPoint.volume G hq hqpos hspan) := by
  intro s t hs ht x y
  change p (s + t) x y = ∫ z : Fin N → ℝ, p s x z * p t z y ∂volume
  exact (h s t hs ht x y).symm

end HeatKernel.Gaussian
