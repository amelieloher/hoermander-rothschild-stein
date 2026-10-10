-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Layer representations of linear and squared distance tents

The layer parameter ranges over the unit interval. Nonnegative integration
allows the same representations to be used for energy densities without
assuming their integrability in advance.
-/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- The linear tent is the length of the interval of layers containing a point. -/
theorem lintegral_indicator_layers_eq_tent {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ s in Ioo (0 : ℝ) 1, (Ioi a).indicator (fun _ => (1 : ℝ≥0∞)) s) =
      ENNReal.ofReal (max (1 - a) 0) := by
  rw [setLIntegral_indicator measurableSet_Ioi]
  have he : Ioi a ∩ Ioo (0 : ℝ) 1 = Ioo a 1 := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h, _, h1⟩; exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩; exact ⟨h, lt_of_le_of_lt ha h, h1⟩
  simp only [he, lintegral_const, Measure.restrict_apply_univ, one_mul, Real.volume_Ioo]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - a))]

/-- The squared tent is represented by layers weighted by twice the remaining radius. -/
theorem lintegral_weighted_layers_eq_tent_sq {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ s in Ioo (0 : ℝ) 1,
      (Ioi a).indicator (fun s => ENNReal.ofReal (2 * (1 - s))) s) =
      ENNReal.ofReal (max (1 - a) 0 ^ 2) := by
  rw [setLIntegral_indicator measurableSet_Ioi]
  have he : Ioi a ∩ Ioo (0 : ℝ) 1 = Ioo a 1 := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h, _, h1⟩; exact ⟨h, h1⟩
    · rintro ⟨h, h1⟩; exact ⟨h, lt_of_le_of_lt ha h, h1⟩
  rw [he]
  by_cases ha1 : a < 1
  · have hi : IntegrableOn (fun s : ℝ => 2 * (1 - s)) (Ioo a 1) :=
      (by fun_prop : Continuous (fun s : ℝ => 2 * (1 - s))).integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by change 0 ≤ 2 * (1 - s); nlinarith [hs.2]))]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1.le]
    have heq : (fun s : ℝ => 2 * (1 - s)) = fun s => 2 - 2 * s := by funext s; ring
    rw [heq, intervalIntegral.integral_sub (f := fun _ : ℝ => (2 : ℝ)) (g := fun s : ℝ => 2 * s) (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, _root_.integral_id,
      intervalIntegral.integral_const, max_eq_left (by linarith : 0 ≤ 1 - a)]
    congr 1
    simp only [smul_eq_mul]
    ring
  · rw [Ioo_eq_empty ha1, Measure.restrict_empty, lintegral_zero_measure,
      max_eq_right (by linarith : 1 - a ≤ 0)]
    simp

/-- Tonelli converts a measurable layer representation into a weighted energy identity. -/
theorem lintegral_mul_eq_lintegral_layers {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d : α → ℝ} (hd : Measurable d)
    {k : ℝ → ℝ≥0∞} (hk : Measurable k) {w g : α → ℝ≥0∞}
    (hg : Measurable g)
    (hw : ∀ x, w x = ∫⁻ s in Ioo (0 : ℝ) 1, (Ioi (d x)).indicator k s) :
    (∫⁻ x, w x * g x ∂μ) =
      ∫⁻ s in Ioo (0 : ℝ) 1, k s * ∫⁻ x in {x | d x < s}, g x ∂μ := by
  have he : (fun x => w x * g x) = fun x =>
      ∫⁻ s in Ioo (0 : ℝ) 1, (Ioi (d x)).indicator k s * g x := by
    funext x
    rw [hw x, lintegral_mul_const _ (hk.indicator measurableSet_Ioi)]
  rw [he, lintegral_lintegral_swap]
  · apply lintegral_congr
    intro s
    rw [← lintegral_indicator (measurableSet_lt hd measurable_const),
      ← lintegral_const_mul _ (hg.indicator (measurableSet_lt hd measurable_const))]
    apply lintegral_congr
    intro x
    by_cases hx : d x < s <;> simp [hx]
  · exact Measurable.aemeasurable (by
      apply Measurable.mul
      · exact Measurable.ite (measurableSet_lt (hd.comp measurable_fst) measurable_snd)
          (hk.comp measurable_snd) measurable_const
      · exact hg.comp measurable_fst)

end HeatKernel.Sobolev
