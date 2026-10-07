-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExponentEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric
open scoped NNReal
variable {X : Type*} [MetricSpace X]

/-- The lower Holder class contains the exact input representative. -/
theorem exists_holderRestriction {δ s : ℝ≥0} {o : X} {R : ℝ}
    (hR : 0 < R) (hδs : δ ≤ s) (f : H2.holderFunctions s (ball o R)) :
    ∃ g : H2.holderFunctions δ (ball o R), (g : X → ℝ) = f := by
  refine ⟨⟨(f : X → ℝ), boundedHolder_exponent_mono_ball hR hδs f.property.1,
    f.property.2⟩, rfl⟩

/-- An exponent restriction with its representative equality exposed
through the existence theorem. -/
def chosenHolderRestriction {δ s : ℝ≥0} {o : X} {R : ℝ}
    (hR : 0 < R) (hδs : δ ≤ s) (f : H2.holderFunctions s (ball o R)) :
    H2.holderFunctions δ (ball o R) := (exists_holderRestriction hR hδs f).choose

/-- The chosen restriction preserves the input pointwise. -/
theorem chosenHolderRestriction_coe {δ s : ℝ≥0} {o : X} {R : ℝ}
    (hR : 0 < R) (hδs : δ ≤ s) (f : H2.holderFunctions s (ball o R)) :
    (chosenHolderRestriction hR hδs f : X → ℝ) = f :=
  (exists_holderRestriction hR hδs f).choose_spec

end RothschildStein.H3
