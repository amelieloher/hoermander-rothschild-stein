-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingWeightedSpan
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

/-- Original generator indices retain their coordinate values. -/
theorem paddingGeneratorIndex_val {q d : ℕ} (i : Fin (q + 1)) :
    (paddingGeneratorIndex (d := d) i).val = i.val := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [paddingGeneratorIndex]

/-- The original generator map is injective. -/
theorem paddingGeneratorIndex_injective {q d : ℕ} :
    Function.Injective (paddingGeneratorIndex (q := q) (d := d)) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa only [paddingGeneratorIndex_val] using hv

end RothschildStein.P1
