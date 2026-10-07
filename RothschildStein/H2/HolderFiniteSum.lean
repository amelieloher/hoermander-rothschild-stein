-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.HolderLinear
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped NNReal ENNReal BigOperators
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- Finite sums obey the triangle inequality for the full Hölder norm. -/
theorem boundedHolderNorm_sum_le {ι : Type*} (s : Finset ι) (δ : ℝ≥0)
    (U : Set X) (f : ι → X → ℝ) :
    boundedHolderNorm δ U (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, boundedHolderNorm δ U (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change holderSup U (fun _ => 0) + eHolderNorm δ (0 : U → ℝ) ≤ 0
    simp [holderSup]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact boundedHolderNorm_add_le.trans (add_le_add le_rfl ih)

/-- The bounded Hölder space is closed under finite sums. -/
theorem boundedHolder_sum {ι : Type*} (s : Finset ι) (δ : ℝ≥0)
    (U : Set X) (f : ι → X → ℝ) (hf : ∀ i ∈ s, BoundedHolder δ U (f i)) :
    BoundedHolder δ U (fun x => ∑ i ∈ s, f i x) := by
  exact (boundedHolderNorm_sum_le s δ U f).trans_lt
    (ENNReal.sum_lt_top.mpr hf)
end RothschildStein.H2
