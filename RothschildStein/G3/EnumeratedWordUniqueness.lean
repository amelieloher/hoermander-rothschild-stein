-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedWordProperties
public import Mathlib.Data.List.Nodup
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- A homogeneous layer lists every underlying word once. -/
theorem layerWordEnumeration_nodup (a s : ℕ) (p : Fin a → ℕ+) (k : ℕ) :
    (layerWordEnumeration a s p k).Nodup := by
  classical
  apply List.Nodup.map
  · intro I J h
    apply Subtype.ext
    exact Subtype.ext h
  · exact Finset.nodup_toList _

/-- Distinct homogeneous layers cannot repeat an underlying word. -/
theorem correctionWordEnumeration_nodup (a s : ℕ) (p : Fin a → ℕ+) (n : ℕ) :
    (correctionWordEnumeration a s p n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ n ih =>
    apply ih.append (layerWordEnumeration_nodup a s p (n+1))
    rw [List.disjoint_left]
    intro I hI hJ
    obtain ⟨J,_,rfl⟩ := List.mem_map.mp hJ
    have hw := (correctionWordEnumeration_mem J.val.val hI).2
    have he := J.property
    omega
end RothschildStein.G3
