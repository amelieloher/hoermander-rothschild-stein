-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedArcCount
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Enumerated words have positive weight and lie below their layer cutoff. -/
theorem correctionWordEnumeration_mem {a s n : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hI : I ∈ correctionWordEnumeration a s p n) :
    I ≠ [] ∧ wordWeight p I ≤ n := by
  induction n with
  | zero => simp [correctionWordEnumeration] at hI
  | succ n ih =>
    rcases List.mem_append.mp hI with hI | hI
    · exact ⟨(ih hI).1, (ih hI).2.trans (Nat.le_succ n)⟩
    · obtain ⟨J,_,rfl⟩ := List.mem_map.mp hI
      exact ⟨layerWord_ne_nil (by omega) J,J.property.le⟩

/-- Every nonempty retained word occurs in the layer enumeration. -/
theorem correctionWordEnumeration_contains {a s n : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hne : I ≠ []) (hs : wordWeight p I ≤ s)
    (hn : wordWeight p I ≤ n) : I ∈ correctionWordEnumeration a s p n := by
  induction n with
  | zero =>
    have hl := length_le_weight p I
    have he : I.length = 0 := by omega
    exact (hne (List.length_eq_zero_iff.mp he)).elim
  | succ n ih =>
    by_cases hprev : wordWeight p I ≤ n
    · exact List.mem_append_left _ (ih hprev)
    · have hk : wordWeight p I = n+1 := by omega
      apply List.mem_append_right
      change I ∈ (Finset.univ : Finset (LayerWord a s p (n+1))).toList.map (fun J => J.val.val)
      exact List.mem_map.mpr ⟨⟨boundedWord p I hs,hk⟩,by simp,rfl⟩

end RothschildStein.G3
