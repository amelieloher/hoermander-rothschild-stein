-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldDefs
public import Hormander.Interface.LieWordEval

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Original generator indices embed in the padded family,
keeping the drift at zero and omitting the appended diffusion indices. -/
def paddingGeneratorIndex {q d : ℕ} : Fin (q + 1) → Fin (q + d + 1) :=
  Fin.cases 0 (fun i => (Fin.castAdd d i).succ)

/-- The original bracket syntax embeds recursively in the
padded generator family, preserving each bracket operation. -/
def paddingLieWord {q d : ℕ} : Hormander.Interface.LieWord q → Hormander.Interface.LieWord (q + d)
  | .generator i => .generator (paddingGeneratorIndex (d := d) i)
  | .bracket p r => .bracket (paddingLieWord p) (paddingLieWord r)

/-- An embedded original generator denotes precisely its
original field extended with zero added-coordinate components. -/
theorem paddingVectorFields_generatorIndex {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin (q + 1)) :
    paddingVectorFields (d := d) X (paddingGeneratorIndex (d := d) i) =
      paddingBaseField (d := d) (X i) := by
  refine Fin.cases ?_ ?_ i
  · simp [paddingGeneratorIndex, paddingVectorFields_zero]
  · intro j
    simp [paddingGeneratorIndex, paddingVectorFields_original]

end RothschildStein.P1
