-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ControlAdjointExpansion
public import RothschildStein.G4.ShortBracketReduction
public import RothschildStein.G4.IteratedGeneratorDifferentiation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The actual binary expression for ordered short-field adjoints;
no reduction of intermediate brackets is performed. -/
def orderedShortAdjointWord {k s : ℕ} (w : Fin (k + 1) → ℕ+)
    (J : ShortWord w s) : List (ShortWord w s) → Hormander.Interface.LieWord k
  | [] => shortBinaryWord w J
  | I :: L => .bracket (shortBinaryWord w I) (orderedShortAdjointWord w J L)

/-- The binary expression evaluates to the whole ordered adjoint. -/
theorem orderedShortAdjointWord_eval {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (J : ShortWord w s) (L : List (ShortWord w s)) :
    Hormander.lieWordEval X (orderedShortAdjointWord w J L) =
      orderedAdjoints (shortField w X) L (shortField w X J) := by
  induction L with
  | nil => exact shortBinaryWord_eval w X J
  | cons I L ih =>
    simp only [orderedShortAdjointWord, Hormander.lieWordEval,
      shortBinaryWord_eval, ih, orderedAdjoints]

/-- The whole binary bracket has exactly the sum of its short
input weights, including the final field. -/
theorem orderedShortAdjointWord_weight {k s : ℕ} (w : Fin (k + 1) → ℕ+)
    (J : ShortWord w s) (L : List (ShortWord w s)) :
    (G1.binaryWeight w (orderedShortAdjointWord w J L) : ℤ) =
      (shortWeight w J : ℕ) + derivativeWeight (shortWeight w) L := by
  induction L with
  | nil => simp [orderedShortAdjointWord, shortBinaryWord_weight, derivativeWeight]
  | cons I L ih =>
    simp only [orderedShortAdjointWord, G1.binaryWeight, Nat.cast_add,
      shortBinaryWord_weight, ih, derivativeWeight, List.map_cons, List.sum_cons]
    ring

end RothschildStein.G4
