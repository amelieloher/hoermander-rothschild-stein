-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OrderedAdjointBinaryWords
public import RothschildStein.G4.WeightedAdjointControls
public import RothschildStein.G4.UniformBinaryCoefficientBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- An ordered adjoint with j brackets of short fields has
primitive weight at most (j+1)s. -/
theorem orderedShortAdjointWord_weight_le {k s : ℕ} (w : Fin (k + 1) → ℕ+)
    (J : ShortWord w s) (L : List (ShortWord w s)) :
    G1.binaryWeight w (orderedShortAdjointWord w J L) ≤ (L.length + 1) * s := by
  induction L with
  | nil =>
    simpa only [orderedShortAdjointWord, shortBinaryWord_weight, List.length_nil,
      zero_add, one_mul, shortWeight, PNat.mk_coe] using ((mem_shortWordFamily_iff w J.val).mp J.property).2
  | cons I L ih =>
    have hI := ((mem_shortWordFamily_iff w I.val).mp I.property).2
    simp only [orderedShortAdjointWord, G1.binaryWeight, shortBinaryWord_weight,
      List.length_cons]
    calc
      _ ≤ s + (L.length + 1) * s := Nat.add_le_add hI ih
      _ = _ := by ring

end RothschildStein.G4
