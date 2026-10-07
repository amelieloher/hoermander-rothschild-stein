-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CommutatorIncrement
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The negative exponential product has a positive weighted increment
(BB Lemma 9.26, pp. 417–419). -/
theorem negativeExpProduct_weight_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast k A)
    (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (min k l) (finiteExp (-A) * finiteExp (-B) - 1) := by
  have hAn : FiniteOrderAtLeast k (-A) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element k) hA
  have hBn : FiniteOrderAtLeast l (-B) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element l) hB
  have hf := finiteExp_sub_one_weight_order hAn
  have hg := finiteExp_sub_one_weight_order hBn
  have he : finiteExp (-A) * finiteExp (-B) - 1 =
      (finiteExp (-A) - 1) + (finiteExp (-B) - 1) +
        (finiteExp (-A) - 1) * (finiteExp (-B) - 1) := by noncomm_ring
  rw [he]
  exact finiteOrderAtLeast_add
    (finiteOrderAtLeast_add (finiteOrderAtLeast_mono hf (Nat.min_le_left _ _))
      (finiteOrderAtLeast_mono hg (Nat.min_le_right _ _)))
    (finiteOrderAtLeast_mono (finiteOrderAtLeast_mul hf hg)
      ((Nat.min_le_left k l).trans (Nat.le_add_right k l)))

/-- The signed exponential commutator has the positive leading
coefficient [A,B], with an extra positive input in every remainder term
(BB Lemma 9.26, pp. 417–419; corrected intermediate sign). -/
theorem commutatorIncrement_sub_lie_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l + min k l) (commutatorIncrement A B - ⁅A,B⁆) := by
  rw [commutatorIncrement_eq (finiteOrderAtLeast_mono hA hk) (finiteOrderAtLeast_mono hB hl)]
  have he : ⁅finiteExp A, finiteExp B⁆ * (finiteExp (-A) * finiteExp (-B)) - ⁅A,B⁆ =
      (⁅finiteExp A, finiteExp B⁆ - ⁅A,B⁆) * (finiteExp (-A) * finiteExp (-B)) +
        ⁅A,B⁆ * (finiteExp (-A) * finiteExp (-B) - 1) := by noncomm_ring
  rw [he]
  exact finiteOrderAtLeast_add
    (by simpa only [Nat.add_zero] using
      (finiteOrderAtLeast_mul (exponential_bracket_sub_lie_order hA hB)
        (finiteOrderAtLeast_zero (finiteExp (-A) * finiteExp (-B)))))
    (finiteOrderAtLeast_mul (finiteOrderAtLeast_lie hA hB) (negativeExpProduct_weight_order hA hB))

/-- Taking the finite logarithm preserves the corrected leading bracket
and summed weight (BB Lemma 9.26, pp. 417–419). -/
theorem commutatorLog_sub_lie_order {a s k l : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) {A B : FiniteWordAlgebra a s p} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l + min k l)
      (logApprox (commutatorIncrement A B) s - ⁅A,B⁆) := by
  have ht := logApprox_sub_input_weight_order (commutatorIncrement_weight_order hk hl hA hB) hs
  have he : logApprox (commutatorIncrement A B) s - ⁅A,B⁆ =
      (logApprox (commutatorIncrement A B) s - commutatorIncrement A B) +
        (commutatorIncrement A B - ⁅A,B⁆) := by abel
  rw [he]
  exact finiteOrderAtLeast_add (finiteOrderAtLeast_mono ht (by
    have h := Nat.min_le_left k l; omega)) (commutatorIncrement_sub_lie_order hk hl hA hB)
end RothschildStein.G3
