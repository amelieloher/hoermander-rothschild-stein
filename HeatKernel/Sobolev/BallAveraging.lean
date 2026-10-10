-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.AveragingKernel
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic

/-!
# Averaging over metric balls of equal measure

An equal-volume hypothesis makes the normalized ball kernel have column mass
one. The resulting L¹-to-L² estimate uses no Poincaré inequality.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HeatKernel.Sobolev

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] {μ : Measure α}

/-- The nonnegative normalized kernel of a metric ball. -/
noncomputable def ballAverageKernel (s : ℝ) (V : ℝ≥0∞) (x y : α) : ℝ≥0∞ :=
  if dist x y < s then V⁻¹ else 0

/-- The normalized ball kernel is jointly measurable. -/
theorem measurable_ballAverageKernel (s : ℝ) (V : ℝ≥0∞) :
    Measurable (Function.uncurry (ballAverageKernel (α := α) s V)) := by
  unfold ballAverageKernel Function.uncurry
  exact Measurable.ite (measurableSet_lt measurable_dist measurable_const)
    measurable_const measurable_const

omit [SecondCountableTopology α] in
/-- Equal ball measures give unit column mass for the normalized ball kernel. -/
theorem lintegral_ballAverageKernel_eq_one {s : ℝ} {V : ℝ≥0∞}
    (hV : V ≠ 0) (hVtop : V ≠ ⊤) (hvolume : ∀ x : α, μ (ball x s) = V) (y : α) :
    (∫⁻ x, ballAverageKernel s V x y ∂μ) = 1 := by
  classical
  have heq : (fun x => ballAverageKernel s V x y) =
      (ball y s).indicator (fun _ => V⁻¹) := by
    funext x
    change (if dist x y < s then V⁻¹ else 0) =
      (if x ∈ ball y s then V⁻¹ else 0)
    simp only [mem_ball, dist_comm]
  rw [heq, lintegral_indicator_const measurableSet_ball, hvolume]
  exact ENNReal.inv_mul_cancel hV hVtop

end HeatKernel.Sobolev
