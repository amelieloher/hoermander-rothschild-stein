-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CommutatorPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.S
variable {α κ : Type*}

/-- Any kernel property satisfied by the one-letter base and
preserved by transfer holds for every recursively constructed pair
(BB (2.10)–(2.12), pp. 77–79). -/
theorem friedrichsCommutatorPairs_kernel_property (base : α → κ)
    (transfer : α → κ → κ) (P : κ → Prop) (hbase : ∀ j, P (base j))
    (htransfer : ∀ j k, P k → P (transfer j k)) (I : List α)
    {p : κ × List α} (hp : p ∈ friedrichsCommutatorPairs base transfer I) : P p.1 := by
  induction I generalizing p with
  | nil => simp [friedrichsCommutatorPairs] at hp
  | cons j I ih =>
    simp only [friedrichsCommutatorPairs,List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with (⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩) | rfl
    · exact ih (p := a) ha
    · exact htransfer j a.1 (ih (p := a) ha)
    · exact hbase j

end RothschildStein.S
