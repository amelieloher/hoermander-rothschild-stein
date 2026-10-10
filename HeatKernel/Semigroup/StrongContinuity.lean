-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.BoundedHeatOperators

/-! # Strong continuity of heat operators

A weighted operator estimate gives continuity on the resolvent range. Contractivity extends
this conclusion to its closure.
-/

@[expose] public section
open Set
open scoped NNReal

namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem dist_heatOperator_apply_le (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (t : ℝ≥0) (x y : E) :
    dist (heatOperator R t x) (heatOperator R t y) ≤ dist x y := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact ((heatOperator R t).le_opNorm (x - y)).trans
    (by simpa using (mul_le_mul_of_nonneg_right (norm_heatOperator_le R hspec t)
      (norm_nonneg (x - y))))

theorem dist_heatOperator_range_le (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (s t : ℝ≥0) (y : E) :
    dist (heatOperator R t (R y)) (heatOperator R s (R y)) ≤ dist t s * ‖y‖ := by
  calc
    _ = ‖((heatOperator R t - heatOperator R s) * R) y‖ := by
      rw [dist_eq_norm, mul_apply_eq_comp, sub_apply]
    _ ≤ ‖(heatOperator R t - heatOperator R s) * R‖ * ‖y‖ :=
      ((heatOperator R t - heatOperator R s) * R).le_opNorm y
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_heatOperator_sub_mul_le R hR hspec s t)
      (norm_nonneg y)

theorem continuous_heatOperator_apply_of_denseRange (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (x : E) : Continuous (fun t : ℝ≥0 => heatOperator R t x) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨y, hy⟩ := hdense.exists_dist_lt x (show 0 < ε / 4 by positivity)
  refine ⟨ε / (2 * (‖y‖ + 1)), by positivity, ?_⟩
  intro t ht
  have hm : dist t s * ‖y‖ < ε / 2 := by
    have hprod := (lt_div_iff₀ (show 0 < 2 * (‖y‖ + 1) by positivity)).mp ht
    have hdist := dist_nonneg (x := t) (y := s)
    nlinarith [norm_nonneg y]
  calc
    dist (heatOperator R t x) (heatOperator R s x) ≤
        dist (heatOperator R t x) (heatOperator R t (R y)) +
          dist (heatOperator R t (R y)) (heatOperator R s (R y)) +
          dist (heatOperator R s (R y)) (heatOperator R s x) :=
      dist_triangle4 _ _ _ _
    _ ≤ dist x (R y) + dist t s * ‖y‖ + dist (R y) x := by
      gcongr
      · exact dist_heatOperator_apply_le R hspec t x (R y)
      · exact dist_heatOperator_range_le R hR hspec s t y
      · exact dist_heatOperator_apply_le R hspec s (R y) x
    _ < ε := by rw [dist_comm (R y) x]; linarith

end HeatKernel
