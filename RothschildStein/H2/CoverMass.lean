-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Whitney
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Integrating countable finite overlap bounds the sum of
ball measures by N times the covered-set measure (BB Lemma 7.34, p. 324).
The ambient measure need not be σ-finite. -/
theorem sum_ball_measure_le_overlap (μ : Measure X) {A u : Set X} (hA : MeasurableSet A)
    (hu : u.Countable) (r : X → ℝ) (N : ℝ≥0∞)
    (hinside : ∀ z ∈ u, ball z (r z) ⊆ A)
    (hoverlap : ∀ x : X, (∑' z : X, if z ∈ u ∧ x ∈ ball z (r z)
      then (1 : ℝ≥0∞) else 0) ≤ N) :
    (∑' z : u, μ (ball (z : X) (r z))) ≤ N * μ A := by
  let : Countable u := hu.to_subtype
  let H : u → X → ℝ≥0∞ := fun z => (ball (z : X) (r z)).indicator (fun _ => 1)
  have hHm (z : u) : Measurable (H z) := measurable_const.indicator isOpen_ball.measurableSet
  have hpoint (x : X) : (∑' z : u, H z x) ≤ N := by
    have hh := ENNReal.tsum_comp_le_tsum_of_injective (f := fun z : u => (z : X)) Subtype.val_injective
      (fun z : X => if z ∈ u ∧ x ∈ ball z (r z) then (1 : ℝ≥0∞) else 0)
    have he : (∑' z : u, H z x) =
        ∑' z : u, if (z : X) ∈ u ∧ x ∈ ball (z : X) (r z) then (1 : ℝ≥0∞) else 0 := by
      apply tsum_congr
      intro z
      simp only [H, z.property, true_and, Set.indicator_apply]
    rw [he]
    exact hh.trans (hoverlap x)
  have hbound (x : X) : (∑' z : u, H z x) ≤ A.indicator (fun _ => N) x := by
    by_cases hx : x ∈ A
    · simpa only [Set.indicator_of_mem hx] using hpoint x
    · have he : ∀ z : u, H z x = 0 := by
        intro z
        exact Set.indicator_of_notMem (fun hb => hx (hinside z z.property hb)) _
      simp only [he, tsum_zero, Set.indicator_of_notMem hx, le_refl]
  calc
    _ = ∑' z : u, ∫⁻ x, H z x ∂μ := by
      apply tsum_congr
      intro z
      rw [lintegral_indicator_const isOpen_ball.measurableSet]
      simp
    _ = ∫⁻ x, ∑' z : u, H z x ∂μ := (lintegral_tsum (fun z => (hHm z).aemeasurable)).symm
    _ ≤ ∫⁻ x, A.indicator (fun _ => N) x ∂μ := lintegral_mono hbound
    _ = N * μ A := lintegral_indicator_const hA N

end RothschildStein.H2
