-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CommutatorLeadingTerm
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The three successive BCH combinations give exactly the logarithm
of the four signed primitive exponentials (BB Lemma 9.26, pp. 417–419). -/
theorem finiteBCH_commutator_eq_log {a s : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast 1 A)
    (hB : FiniteOrderAtLeast 1 B) :
    finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B) =
      logApprox (commutatorIncrement A B) s := by
  have hAn : FiniteOrderAtLeast 1 (-A) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element 1) hA
  have hBn : FiniteOrderAtLeast 1 (-B) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element 1) hB
  have hAB := finiteBCH_order hA hB
  have hABA := finiteBCH_order hAB hAn
  have hC := finiteBCH_order hABA hBn
  have hv := finiteOrderAtLeast_mono (commutatorIncrement_weight_order le_rfl le_rfl hA hB)
    (by omega : 1 ≤ 1 + 1)
  apply finiteExp_injective_positive hC (logApprox_order hv s).1
  rw [finiteExp_BCH hABA hBn, finiteExp_BCH hAB hAn, finiteExp_BCH hA hB,
    finiteExp_logApprox hv, commutatorIncrement]
  abel

/-- The BCH commutator has summed weight (BB Lemma 9.26, pp. 417–419). -/
theorem finiteBCH_commutator_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l) (finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B)) := by
  rw [finiteBCH_commutator_eq_log (finiteOrderAtLeast_mono hA hk) (finiteOrderAtLeast_mono hB hl)]
  exact logApprox_weight_order (commutatorIncrement_weight_order hk hl hA hB) s

/-- The BCH commutator's leading coefficient has BB's positive word
sign, with remainder of strictly greater weight (BB pp. 417–419). -/
theorem finiteBCH_commutator_sub_lie_order {a s k l : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) {A B : FiniteWordAlgebra a s p} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l + 1)
      (finiteBCH (finiteBCH (finiteBCH A B) (-A)) (-B) - ⁅A,B⁆) := by
  rw [finiteBCH_commutator_eq_log (finiteOrderAtLeast_mono hA hk) (finiteOrderAtLeast_mono hB hl)]
  exact finiteOrderAtLeast_mono (commutatorLog_sub_lie_order hs hk hl hA hB) (by omega)
end RothschildStein.G3
