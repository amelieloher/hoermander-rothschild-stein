-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Tactic.NormNum

/-! Finite packing bounds from disjointness and a lower measure bound. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Disjoint measurable pieces of measure at least c in one containing set pay c for
each member. No regularity or doubling assumption is needed for this counting step. -/
theorem card_mul_le_measure_of_disjoint {E ι : Type*} [MeasurableSpace E]
    (μ : Measure E) (s : Finset ι) {B : ι → Set E} {U : Set E} {c : ℝ≥0∞}
    (hdisj : (s : Set ι).PairwiseDisjoint B)
    (hmeas : ∀ i ∈ s, MeasurableSet (B i))
    (hsub : ∀ i ∈ s, B i ⊆ U) (hmeasure : ∀ i ∈ s, c ≤ μ (B i)) :
    (s.card : ℝ≥0∞) * c ≤ μ U := by
  calc
    (s.card : ℝ≥0∞) * c = ∑ _i ∈ s, c := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, μ (B i) := Finset.sum_le_sum hmeasure
    _ = μ (⋃ i ∈ s, B i) := (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ μ U := measure_mono (iUnion₂_subset hsub)

/-- A finite containing measure bounds the cardinality when every disjoint member has
a common positive finite measure lower bound. -/
theorem card_le_of_disjoint_measure_bound {E ι : Type*} [MeasurableSpace E]
    (μ : Measure E) (s : Finset ι) {B : ι → Set E} {U : Set E} {c : ℝ≥0∞} {K : ℕ}
    (hdisj : (s : Set ι).PairwiseDisjoint B)
    (hmeas : ∀ i ∈ s, MeasurableSet (B i))
    (hsub : ∀ i ∈ s, B i ⊆ U) (hmeasure : ∀ i ∈ s, c ≤ μ (B i))
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (hU : μ U ≤ K * c) : s.card ≤ K := by
  have hh := mul_le_mul_left
    ((card_mul_le_measure_of_disjoint μ s hdisj hmeas hsub hmeasure).trans hU) c⁻¹
  simp only [mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one] at hh
  exact_mod_cast hh

end HeatKernel
