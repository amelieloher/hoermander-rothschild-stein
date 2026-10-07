-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZGood
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

omit [Countable ι] in
theorem czGood_nonneg (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) : ∀ᵐ x ∂μ, 0 ≤ czGood μ B f x := by
  filter_upwards [hf] with x hx
  apply add_nonneg
  · by_cases ha : x ∈ (⋃ i, B i)ᶜ
    · simpa only [indicator_of_mem ha] using hx
    · rw [indicator_of_notMem ha]
  · exact tsum_nonneg fun i => czReplacement_nonneg μ B hfinite f hf i x

omit [Countable ι] in
theorem czGood_bound (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    {L N L₀ : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N)
    (havg : ∀ i, czAverage μ B f i ≤ L)
    (hoverlap : ∀ x, coverMultiplicity B x ≤ ENNReal.ofReal N)
    (hgood : ∀ᵐ x ∂μ, x ∉ ⋃ i, B i → f x ≤ L₀) :
    ∀ᵐ x ∂μ, czGood μ B f x ≤ max L₀ (N * L) := by
  filter_upwards [hgood] with x hx
  have hc : ((hfinite x).toFinset.card : ℝ) ≤ N := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hoverlap x)
    simpa only [coverMultiplicity_eq_card B x (hfinite x), ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal hN] using ht
  have hs : (∑' i, czReplacement μ B f i x) ≤ N * L := by
    rw [tsum_eq_sum (s := (hfinite x).toFinset)]
    · calc
        _ ≤ ∑ i ∈ (hfinite x).toFinset, L := by
          apply Finset.sum_le_sum
          intro i hi
          have hm : x ∈ B i := by simpa using hi
          simpa only [czReplacement, indicator_of_mem hm] using havg i
        _ = ((hfinite x).toFinset.card : ℝ) * L := by simp
        _ ≤ N * L := mul_le_mul_of_nonneg_right hc hL
    · intro i hi
      have hm : x ∉ B i := by simpa using hi
      simp [czReplacement, hm]
  by_cases ha : x ∈ ⋃ i, B i
  · change (⋃ i, B i)ᶜ.indicator f x + _ ≤ _
    rw [indicator_of_notMem (show x ∉ (⋃ i, B i)ᶜ from fun h => h ha)]
    rw [zero_add]
    exact hs.trans (le_max_right _ _)
  · have hz : ∀ i, czReplacement μ B f i x = 0 := by
      intro i
      have hm : x ∉ B i := fun h => ha (mem_iUnion.mpr ⟨i, h⟩)
      simp [czReplacement, hm]
    change (⋃ i, B i)ᶜ.indicator f x + _ ≤ _
    rw [indicator_of_mem (show x ∈ (⋃ i, B i)ᶜ from ha)]
    simp only [hz, tsum_zero, add_zero]
    exact (hx ha).trans (le_max_left _ _)

theorem czBad_memLp (μ : Measure X) (B : ι → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hμ : ∀ i, μ (B i) ≠ ∞)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    {p : ℝ≥0∞} (hf : MemLp f p μ) (i : ι) : MemLp (czBad μ B f i) p μ := by
  have hw : MemLp (czWeighted B f i) p μ := by
    refine hf.of_le (hf.aestronglyMeasurable.mul
      (measurable_coverWeight B hB i).aestronglyMeasurable) ?_
    exact ae_of_all _ fun x => by
      rw [czWeighted, norm_mul,
        Real.norm_of_nonneg (coverWeight_nonneg_le_one B x (hfinite x) i).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (coverWeight_nonneg_le_one B x (hfinite x) i).2
  exact hw.sub (memLp_indicator_const p (hB i) (czAverage μ B f i) (Or.inr (hμ i)))

omit [Countable ι] in
/-- Partial sums of bad pieces have the L² dominator used for the weak-type estimate. -/
theorem czBad_partial_bound (μ : Measure X) (B : ι → Set X)
    (hfinite : ∀ x, {i | x ∈ B i}.Finite) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) (s : Finset ι) :
    ∀ᵐ x ∂μ, ‖∑ i ∈ s, czBad μ B f i x‖ ≤ f x + czGood μ B f x := by
  filter_upwards [hf] with x hx
  have hw : ∀ i, 0 ≤ czWeighted B f i x := fun i => czWeighted_nonneg B hfinite f hx i
  have hr : ∀ i, 0 ≤ czReplacement μ B f i x := fun i => czReplacement_nonneg μ B hfinite f hf i x
  have hws : Summable (fun i => czWeighted B f i x) := summable_of_hasFiniteSupport (czWeighted_finite_support B hfinite f x)
  have hrs : Summable (fun i => czReplacement μ B f i x) := summable_of_hasFiniteSupport (czReplacement_finite_support μ B hfinite f x)
  have hsum : (∑' i, czWeighted B f i x) + (∑' i, czReplacement μ B f i x) ≤
      f x + czGood μ B f x := by
    rw [czWeighted_sum B hfinite]
    change (⋃ i, B i).indicator f x + _ ≤ f x + ((⋃ i, B i)ᶜ.indicator f x + _)
    by_cases ha : x ∈ ⋃ i, B i
    · simp only [Set.indicator, Set.mem_compl_iff, ha, not_true_eq_false, ite_true, ite_false, zero_add, le_refl]
    · simp only [Set.indicator, Set.mem_compl_iff, ha, not_false_eq_true, ite_true, ite_false]
      linarith
  calc
    _ ≤ ∑ i ∈ s, ‖czBad μ B f i x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, (czWeighted B f i x + czReplacement μ B f i x) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [czBad, Real.norm_of_nonneg (hw i), Real.norm_of_nonneg (hr i)] using
        (norm_sub_le (czWeighted B f i x) (czReplacement μ B f i x))
    _ = (∑ i ∈ s, czWeighted B f i x) + ∑ i ∈ s, czReplacement μ B f i x := Finset.sum_add_distrib
    _ ≤ (∑' i, czWeighted B f i x) + ∑' i, czReplacement μ B f i x :=
      add_le_add (hws.sum_le_tsum s (fun i hi => hw i)) (hrs.sum_le_tsum s (fun i hi => hr i))
    _ ≤ _ := hsum

end RothschildStein.H2
