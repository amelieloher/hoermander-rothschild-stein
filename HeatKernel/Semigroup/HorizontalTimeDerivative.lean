-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2PositiveTimeContinuity
public import HeatKernel.Semigroup.HorizontalPositiveTimeDomain
public import HeatKernel.Semigroup.SemigroupDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Strong time derivatives of the horizontal heat flow -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem continuousAt_horizontalHeatOperator_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => horizontalHeatOperator ⊤ X s.toNNReal) t :=
  continuousAt_realL2HeatOperator_pos _ _ (horizontalFormResolvent_isPositive ⊤ X)
    (norm_horizontalFormResolvent_le_one ⊤ X) ht

theorem continuousAt_horizontalHeatGeneratorOperator_pos {t : ℝ} (ht : 0 < t) :
    ContinuousAt (horizontalHeatGeneratorOperator ⊤ X) t :=
  continuousAt_realL2HeatGeneratorOperator_pos _ _ (horizontalFormResolvent_isPositive ⊤ X)
    (norm_horizontalFormResolvent_le_one ⊤ X) ht

theorem hasDerivAt_horizontalHeatOperator_on_domain
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u g : SpatialL2 (N := N) ⊤)
    (hg : horizontalFormResolvent ⊤ X (u + g) = u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => horizontalHeatOperator ⊤ X s.toNNReal u)
      (-horizontalHeatOperator ⊤ X t.toNNReal g) t := by
  have hgen := (tendsto_horizontalHeatOperator_univ_differenceQuotient_iff X hX u g).mpr hg
  have hadd (s r : ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r) :
      horizontalHeatOperator ⊤ X (s + r).toNNReal =
        horizontalHeatOperator ⊤ X s.toNNReal * horizontalHeatOperator ⊤ X r.toNNReal := by
    rw [Real.toNNReal_add hs hr, horizontalHeatOperator_add]
  have hd := hasDerivAt_semigroup_apply_of_generator_limit
    (fun s : ℝ => horizontalHeatOperator ⊤ X s.toNNReal) hadd u (-g) hgen ht
    (continuousAt_horizontalHeatOperator_pos X ht)
  simpa only [map_neg] using hd

theorem hasDerivAt_horizontalHeatOperator
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (f : SpatialL2 (N := N) ⊤)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => horizontalHeatOperator ⊤ X s.toNNReal f)
      (-horizontalHeatGeneratorOperator ⊤ X t f) t := by
  let s := t / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hst : s < t := by dsimp [s]; linarith
  have hhalf : t - s = s := by dsimp [s]; ring
  let T := fun r : ℝ => horizontalHeatOperator ⊤ X r.toNNReal
  let u := T s f
  let g := horizontalHeatGeneratorOperator ⊤ X s f
  have hd := hasDerivAt_horizontalHeatOperator_on_domain X hX u g
    (horizontalHeatOperator_generator_equation ⊤ X s hs f) hs
  change HasDerivAt (fun r => T r u) (-T s g) s at hd
  have hd' : HasDerivAt (fun r => T r u) (-T s g) (t - s) := by rw [hhalf]; exact hd
  have hc : HasDerivAt (fun r : ℝ => T (r - s) u) (-T s g) t :=
    hasDerivAt_shift_sub s t hd'
  have hfull : HasDerivAt (fun r => T r f) (-T s g) t := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hst] with r hr
    change horizontalHeatOperator ⊤ X r.toNNReal f =
      horizontalHeatOperator ⊤ X (r - s).toNNReal (horizontalHeatOperator ⊤ X s.toNNReal f)
    rw [← mul_apply_eq_comp, ← horizontalHeatOperator_add,
      ← Real.toNNReal_add (sub_nonneg.mpr hr.le) hs.le]
    simp only [sub_add_cancel]
  have hright := tendsto_horizontalHeatOperator_positiveTime_differenceQuotient X hX t ht f
  have hright' : Tendsto (fun h : ℝ => h⁻¹ • (T (t + h) f - T t f))
      (𝓝[>] 0) (𝓝 (-horizontalHeatGeneratorOperator ⊤ X t f)) := by
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    change h⁻¹ • (horizontalHeatOperator ⊤ X h.toNNReal
      (horizontalHeatOperator ⊤ X t.toNNReal f) - horizontalHeatOperator ⊤ X t.toNNReal f) =
      h⁻¹ • (horizontalHeatOperator ⊤ X (t + h).toNNReal f - horizontalHeatOperator ⊤ X t.toNNReal f)
    rw [add_comm t h, Real.toNNReal_add hh.le ht.le, horizontalHeatOperator_add, mul_apply_eq_comp]
  have he := tendsto_nhds_unique hfull.tendsto_slope_zero_right hright'
  rw [he] at hfull
  exact hfull

theorem contDiffOn_horizontalHeatOperator
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (f : SpatialL2 (N := N) ⊤) :
    ContDiffOn ℝ 1 (fun t : ℝ => horizontalHeatOperator ⊤ X t.toNNReal f) (Ioi 0) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  constructor
  · intro t ht
    exact (hasDerivAt_horizontalHeatOperator X hX f ht).differentiableAt.differentiableWithinAt
  · have hc : ContinuousOn (fun t : ℝ => -horizontalHeatGeneratorOperator ⊤ X t f) (Ioi 0) := by
      intro t ht
      exact ((continuousAt_horizontalHeatGeneratorOperator_pos X ht).clm_apply continuousAt_const).neg.continuousWithinAt
    apply hc.congr
    intro t ht
    exact (hasDerivAt_horizontalHeatOperator X hX f ht).hasDerivWithinAt.derivWithin
      (isOpen_Ioi.uniqueDiffOn t ht)

end HeatKernel
