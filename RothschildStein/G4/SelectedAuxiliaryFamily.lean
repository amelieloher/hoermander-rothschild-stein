-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AuxiliaryControl
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The coefficient family used by the selected-coordinate map:
first the selected frame, then every short word (BB Lemma 9.49, p. 444). -/
def selectedAuxiliaryIndex {m n s : ℕ} (w : Fin m → ℕ+) (B : Fin n → ShortWord w s) :
    Fin (n + Fintype.card (ShortWord w s)) → ShortWord w s :=
  Fin.addCases B (shortIndex w)

/-- The selected coefficient directions give the selected frame fields. -/
theorem selectedAuxiliaryIndex_selected {m n s : ℕ} (w : Fin m → ℕ+)
    (B : Fin n → ShortWord w s) (i : Fin n) :
    selectedAuxiliaryIndex w B (Fin.castAdd (Fintype.card (ShortWord w s)) i) = B i := by
  simp [selectedAuxiliaryIndex]

/-- The auxiliary coefficient directions give the enumerated short fields. -/
theorem selectedAuxiliaryIndex_auxiliary {m n s : ℕ} (w : Fin m → ℕ+)
    (B : Fin n → ShortWord w s) (j : Fin (Fintype.card (ShortWord w s))) :
    selectedAuxiliaryIndex w B (Fin.natAdd n j) = shortIndex w j := by
  simp [selectedAuxiliaryIndex]

end RothschildStein.G4
