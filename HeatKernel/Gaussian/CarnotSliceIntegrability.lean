-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.SliceIntegrability
public import HeatKernel.Gaussian.HomogeneousBounds
import Mathlib.Tactic

/-! # Square slices on Carnot balls

Exact volume scaling and properness discharge the geometric assumptions in
continuity and time integrability of spatial square slices.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric RothschildStein
namespace HeatKernel.Gaussian

/-- Positive-radius Carnot balls have finite measure. -/
theorem carnot_volume_ball_ne_top {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r) :
    CarnotPoint.volume G hq hqpos hspan (ball x r) ≠ ⊤ := by
  rw [carnot_volume_ball_eq G hq hqpos hspan hw x hr]
  exact ENNReal.ofReal_ne_top

/-- Carnot endpoint cylinders have integrable spatial square slices under
joint continuity alone. -/
theorem integrableOn_carnot_endpoint_integral_ball_sq {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (y : CarnotPoint G hq hqpos hspan) (v : ℝ × CarnotPoint G hq hqpos hspan → ℝ)
    (hv : ContinuousOn v (Ioi 0 ×ˢ univ)) {t s : ℝ}
    (ht : 0 < t) (hs : s ∈ Icc (t / 2) (2 * t)) :
    let r := Real.sqrt t / 4;
    IntegrableOn (fun σ ↦ ∫ z in ball y (2 * r), v (σ, z) ^ 2
      ∂(CarnotPoint.volume G hq hqpos hspan))
      (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)) := by
  have := CarnotPoint.properSpace G hq hqpos hspan hw
  exact integrableOn_endpoint_integral_ball_sq _ y v hv ht hs
    (carnot_volume_ball_ne_top G hq hqpos hspan hw y (by positivity))

end HeatKernel.Gaussian
