-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.QuantitativeCharts
public import RothschildStein.G1.WeightedTriangle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G1

/-- An actual controlled endpoint chart yields the upper
Euclidean comparison on the explicit inverse-function radius.
Its parameter cost is supplied by the finite primitive schedule,
not by any control-distance topology assumption (BB p. 35). -/
theorem controlDistance_upper_of_endpoint_chart {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    {r P L α : ℝ} (hr : 0 < r) (hP : 0 < P) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hA : ‖(A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ P)
    (hD : ∀ u ∈ ball 0 r, HasFDerivAt f (D u) u)
    (hbound : ∀ u ∈ ball 0 r, ‖D u - (A : _ →L[ℝ] _)‖ ≤ 1 / (2 * P))
    (hcost : ∀ u ∈ ball 0 r,
      controlDistance Ω w X (f 0) (f u) ≤ ENNReal.ofReal (L * ‖u‖ ^ α))
    {y : Fin n → ℝ} (hy : ‖y - f 0‖ ≤ r / (4 * P)) :
    controlDistance Ω w X (f 0) y ≤
      ENNReal.ofReal ((L * (2 * P) ^ α) * ‖y - f 0‖ ^ α) := by
  obtain ⟨e, he, hsource, himage⟩ :=
    chart_exists_openPartialHomeomorph_of_derivative_bound A hr hP hA hD hbound
  have hy' : y ∈ e.target := himage (by simpa only [mem_closedBall, dist_eq_norm] using hy)
  have hu : e.symm y ∈ ball 0 r := by rw [← hsource]; exact e.map_target hy'
  have hfy : f (e.symm y) = y := by rw [← he]; exact e.right_inv hy'
  have hparam : ‖e.symm y‖ ≤ 2 * P * ‖y - f 0‖ := by
    have hp := chart_inverse_parameter_bound A hP hA (convex_ball (0 : Fin n → ℝ) r) hD hbound hu (mem_ball_self hr)
    simpa only [hfy, sub_zero] using hp
  have hp := Real.rpow_le_rpow (norm_nonneg _) hparam hα
  calc
    _ ≤ ENNReal.ofReal (L * ‖e.symm y‖ ^ α) := by simpa only [hfy] using hcost _ hu
    _ ≤ ENNReal.ofReal (L * (2 * P * ‖y - f 0‖) ^ α) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp hL)
    _ = _ := by rw [Real.mul_rpow (by positivity) (norm_nonneg _)]; congr 1; ring

end RothschildStein.G1
