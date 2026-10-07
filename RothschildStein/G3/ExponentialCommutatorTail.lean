-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedExponentialTail
public import RothschildStein.G3.LieFiltration
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The bracket of exponential increments has leading coefficient
[A,B]; its remainder has one extra positive weighted input
(BB Lemma 9.26, pp. 417–419; sign-check calculation). -/
theorem exponential_bracket_sub_lie_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast k A)
    (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l + min k l)
      (⁅finiteExp A, finiteExp B⁆ - ⁅A, B⁆) := by
  have he : ⁅finiteExp A, finiteExp B⁆ - ⁅A, B⁆ =
      ⁅A, expTail B⁆ + ⁅expTail A, B⁆ + ⁅expTail A, expTail B⁆ := by
    rw [finiteExp_eq, finiteExp_eq, Ring.lie_def, Ring.lie_def,
      Ring.lie_def, Ring.lie_def, Ring.lie_def]
    noncomm_ring
  rw [he]
  apply finiteOrderAtLeast_add
  · apply finiteOrderAtLeast_add
    · exact finiteOrderAtLeast_mono (finiteOrderAtLeast_lie hA (expTail_weight_order hB))
        (by have h := Nat.min_le_right k l; omega)
    · exact finiteOrderAtLeast_mono (finiteOrderAtLeast_lie (expTail_weight_order hA) hB)
        (by have h := Nat.min_le_left k l; omega)
  · exact finiteOrderAtLeast_mono
      (finiteOrderAtLeast_lie (expTail_weight_order hA) (expTail_weight_order hB))
      (by have h := Nat.min_le_left k l; omega)

/-- Exponential commutators themselves have the summed input weight
(BB Lemma 9.26, pp. 417–419). -/
theorem exponential_bracket_weight_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast k A)
    (hB : FiniteOrderAtLeast l B) : FiniteOrderAtLeast (k + l) ⁅finiteExp A, finiteExp B⁆ := by
  have he : ⁅finiteExp A, finiteExp B⁆ =
      (⁅finiteExp A, finiteExp B⁆ - ⁅A, B⁆) + ⁅A, B⁆ := by abel
  rw [he]
  exact finiteOrderAtLeast_add
    (finiteOrderAtLeast_mono (exponential_bracket_sub_lie_order hA hB) (by omega))
    (finiteOrderAtLeast_lie hA hB)
end RothschildStein.G3
