-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.NormalizedRow
public import HeatKernel.Gaussian.HomogeneousBounds
import Mathlib.Tactic

/-! # Compact normalized data on Carnot balls

Normalized rows supported on a finite-radius ball have compact support and
belong to both the integrable and square-integrable classes.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
namespace HeatKernel.Gaussian

/-- Restricting any function to a ball in a proper space gives compact support. -/
theorem hasCompactSupport_ball_indicator {X E : Type*} [PseudoMetricSpace X]
    [ProperSpace X] [Zero E] (f : X → E) (x : X) (r : ℝ) :
    HasCompactSupport ((ball x r).indicator f) := by
  apply (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  apply ball_subset_closedBall
  by_contra hn
  exact hz (indicator_of_notMem hn f)

/-- The normalized row on a positive-radius Carnot ball is integrable. -/
theorem integrable_carnot_normalized_row {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (f : CarnotPoint G hq hqpos hspan → ℝ)
    (hf : AEStronglyMeasurable f (CarnotPoint.volume G hq hqpos hspan))
    (hpos : 0 < ∫ z in ball x r, f z ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan)) :
    Integrable ((ball x r).indicator (fun z ↦ f z /
      Real.sqrt (∫ w in ball x r, f w ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan))))
        (CarnotPoint.volume G hq hqpos hspan) := by
  apply memLp_one_iff_integrable.mp
  apply (memLp_normalized_indicator (CarnotPoint.volume G hq hqpos hspan)
    measurableSet_ball f hf hpos).mono_exponent_of_measure_support_ne_top
    (s := ball x r) (fun z hz ↦ indicator_of_notMem hz _)
  · rw [carnot_volume_ball_eq G hq hqpos hspan hw x hr]
    exact ENNReal.ofReal_ne_top
  · norm_num

/-- The normalized row on a Carnot ball has compact support in the horizontal topology. -/
theorem hasCompactSupport_carnot_normalized_row {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) (r : ℝ)
    (f : CarnotPoint G hq hqpos hspan → ℝ) :
    HasCompactSupport ((ball x r).indicator (fun z ↦ f z /
      Real.sqrt (∫ w in ball x r, f w ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan)))) := by
  have := CarnotPoint.properSpace G hq hqpos hspan hw
  exact hasCompactSupport_ball_indicator _ x r

end HeatKernel.Gaussian
