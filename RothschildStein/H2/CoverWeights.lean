-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Multiplicity of a countable measurable covering, as an extended real. -/
def coverMultiplicity (B : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑' i, if x ∈ B i then 1 else 0

/-- Equal shares of the multiplicity on each covering set. -/
def coverWeight (B : ι → Set X) (i : ι) (x : X) : ℝ :=
  if x ∈ B i then (coverMultiplicity B x).toReal⁻¹ else 0

theorem measurable_coverMultiplicity (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (coverMultiplicity B) := by
  exact Measurable.tsum fun i => measurable_const.ite (hB i) measurable_const

theorem measurable_coverWeight (B : ι → Set X) (hB : ∀ i, MeasurableSet (B i)) (i : ι) :
    Measurable (coverWeight B i) := by
  exact ((measurable_coverMultiplicity B hB).ennreal_toReal.inv).ite (hB i) measurable_const

omit [MeasurableSpace X] [Countable ι] in
theorem coverMultiplicity_eq_card (B : ι → Set X) (x : X)
    (hf : {i | x ∈ B i}.Finite) :
    coverMultiplicity B x = (hf.toFinset.card : ℝ≥0∞) := by
  unfold coverMultiplicity
  rw [tsum_eq_sum (s := hf.toFinset)]
  · calc
      _ = ∑ i ∈ hf.toFinset, (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
        simp [hi]
      _ = _ := by simp
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
    simp [hi]

omit [MeasurableSpace X] [Countable ι] in
theorem coverWeight_nonneg_le_one (B : ι → Set X) (x : X)
    (hf : {i | x ∈ B i}.Finite) (i : ι) :
    0 ≤ coverWeight B i x ∧ coverWeight B i x ≤ 1 := by
  unfold coverWeight
  split_ifs with hi
  · rw [coverMultiplicity_eq_card B x hf]
    have hc : 1 ≤ hf.toFinset.card := Finset.one_le_card.mpr ⟨i, by simpa using hi⟩
    simp only [ENNReal.toReal_natCast]
    constructor
    · positivity
    · apply inv_le_one_of_one_le₀
      exact_mod_cast hc
  · simp

omit [MeasurableSpace X] [Countable ι] in
theorem coverWeight_sum (B : ι → Set X) (x : X)
    (hf : {i | x ∈ B i}.Finite) :
    (∑' i, coverWeight B i x) = if x ∈ ⋃ i, B i then 1 else 0 := by
  rw [tsum_eq_sum (s := hf.toFinset)]
  · have he : ∀ i ∈ hf.toFinset, x ∈ B i := by simp
    have hs : (∑ i ∈ hf.toFinset, coverWeight B i x) =
        (hf.toFinset.card : ℝ) * (coverMultiplicity B x).toReal⁻¹ := by
      calc
        _ = ∑ i ∈ hf.toFinset, (coverMultiplicity B x).toReal⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [coverWeight, he i hi]
        _ = _ := by simp
    rw [hs, coverMultiplicity_eq_card B x hf]
    simp only [ENNReal.toReal_natCast]
    by_cases hx : x ∈ ⋃ i, B i
    · have hn : hf.toFinset.Nonempty := by
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        exact ⟨i, by simpa using hi⟩
      simp [hx, ne_of_gt (Finset.card_pos.mpr hn)]
    · have hn : hf.toFinset = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hx (mem_iUnion.mpr ⟨i, by simpa using hi⟩)
      simp [hx, hn]
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hi
    simp [coverWeight, hi]

end RothschildStein.H2
