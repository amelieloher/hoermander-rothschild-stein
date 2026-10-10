-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalHeatOperators
public import HeatKernel.Semigroup.HorizontalMarkovOperators

/-! # Order bounds for full-volume horizontal heat flow -/

@[expose] public section

open MeasureTheory RothschildStein
open scoped NNReal

namespace HeatKernel

/-- Full-volume horizontal heat operators preserve nonnegative L² functions. -/
theorem globalHorizontalHeatOperator_nonneg {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hf : ∀ᵐ x ∂volume, 0 ≤ f x) :
    ∀ᵐ x ∂volume, 0 ≤ globalHorizontalHeatOperator G hq t f x := by
  have hnative : ∀ᵐ x ∂volume, 0 ≤ (globalSpatialL2Equiv n).symm f x := by
    filter_upwards [ae_globalSpatialL2Equiv_symm f, hf] with x hx hfx
    rwa [hx]
  have hpos := horizontalHeatOperator_nonneg (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) t _ hnative
  filter_upwards [ae_globalHorizontalHeatOperator_apply G hq t f, hpos] with x hx hpx
  rwa [hx]

/-- Full-volume horizontal heat operators preserve the upper bound one. -/
theorem globalHorizontalHeatOperator_le_one {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (hf : ∀ᵐ x ∂volume, f x ≤ 1) :
    ∀ᵐ x ∂volume, globalHorizontalHeatOperator G hq t f x ≤ 1 := by
  have hnative : ∀ᵐ x ∂volume, (globalSpatialL2Equiv n).symm f x ≤ 1 := by
    filter_upwards [ae_globalSpatialL2Equiv_symm f, hf] with x hx hfx
    rwa [hx]
  have hbound := horizontalHeatOperator_le_one (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) t _ hnative
  filter_upwards [ae_globalHorizontalHeatOperator_apply G hq t f, hbound] with x hx hbx
  rwa [hx]

/-- Full-volume horizontal heat operators preserve the interval from zero to one. -/
theorem globalHorizontalHeatOperator_submarkov {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hf : ∀ᵐ x ∂volume, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ᵐ x ∂volume, 0 ≤ globalHorizontalHeatOperator G hq t f x ∧
      globalHorizontalHeatOperator G hq t f x ≤ 1 :=
  (globalHorizontalHeatOperator_nonneg G hq t f (hf.mono fun _ h => h.1)).and
    (globalHorizontalHeatOperator_le_one G hq t f (hf.mono fun _ h => h.2))

end HeatKernel
