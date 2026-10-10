-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Set.Card

/-! Nonnegative integral estimates for measurable covers with bounded multiplicity. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace HeatKernel

/-- A finite multiplicity bound controls every finite subfamily's count at a point. -/
theorem card_filter_mem_le_of_overlap_ncard {E ι : Type*} (A : ι → Set E) (x : E)
    (M : ℕ) (hfinite : {i | x ∈ A i}.Finite) (hcard : {i | x ∈ A i}.ncard ≤ M)
    (s : Finset ι) : (s.filter fun i => x ∈ A i).card ≤ M := by
  classical
  have hs : (↑(s.filter fun i => x ∈ A i) : Set ι) ⊆ {i | x ∈ A i} :=
    fun i hi => (Finset.mem_filter.mp hi).2
  simpa only [Set.ncard_coe_finset] using (Set.ncard_le_ncard hs hfinite).trans hcard

/-- The sum of indicator-weighted values is bounded by the overlap multiplicity times
the common value, without any assumption of finiteness on that value. -/
theorem tsum_indicator_le_mul_of_overlap {E ι : Type*} (A : ι → Set E)
    (f : E → ℝ≥0∞) (x : E) (M : ℕ)
    (hcount : ∀ s : Finset ι, (s.filter fun i => x ∈ A i).card ≤ M) :
    (∑' i, (A i).indicator f x) ≤ M * f x := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  calc
    (∑ i ∈ s, (A i).indicator f x) = ∑ _i ∈ s with x ∈ A _i, f x := by
      simp only [Finset.sum_filter, Set.indicator_apply]
    _ = ((s.filter fun i => x ∈ A i).card : ℝ≥0∞) * f x := by simp [nsmul_eq_mul]
    _ ≤ M * f x := mul_le_mul_left (by exact_mod_cast hcount s) (f x)

/-- Bounded overlap controls the sum of all set integrals of a nonnegative measurable
function by the multiplicity times its ambient integral. -/
theorem tsum_setLIntegral_le_mul_lintegral_of_overlap {E ι : Type*} [MeasurableSpace E]
    [Countable ι] (μ : Measure E) (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (f : E → ℝ≥0∞) (hf : AEMeasurable f μ) (M : ℕ)
    (hfinite : ∀ x, {i | x ∈ A i}.Finite) (hcard : ∀ x, {i | x ∈ A i}.ncard ≤ M) :
    (∑' i, ∫⁻ x in A i, f x ∂μ) ≤ M * ∫⁻ x, f x ∂μ := by
  calc
    (∑' i, ∫⁻ x in A i, f x ∂μ) = ∑' i, ∫⁻ x, (A i).indicator f x ∂μ := by
      congr 1
      funext i
      rw [lintegral_indicator (hA i)]
    _ = ∫⁻ x, ∑' i, (A i).indicator f x ∂μ :=
      (lintegral_tsum (fun i => hf.indicator (hA i))).symm
    _ ≤ ∫⁻ x, (M : ℝ≥0∞) * f x ∂μ := lintegral_mono fun x =>
      tsum_indicator_le_mul_of_overlap A f x M
        (card_filter_mem_le_of_overlap_ncard A x M (hfinite x) (hcard x))
    _ = M * ∫⁻ x, f x ∂μ := lintegral_const_mul' _ _ (by simp)

end HeatKernel
