-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHObstruction
public import RothschildStein.G3.EichlerZero
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The rational obstruction depends only on the order-one inputs
(BB (9.80), p. 472). -/
theorem rationalBCHClass_eq_of_sub_order_two {b n : ℕ} {p : Fin b → ℕ+}
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    (a c a' c' : rationalCoefficientLieAlgebra b n p)
    (ha : FiniteOrderAtLeast 2 (a.val - a'.val))
    (hc : FiniteOrderAtLeast 2 (c.val - c'.val)) :
    rationalBCHClass a c = rationalBCHClass a' c' := by
  rw [rationalBCHClass_eq_top hLow, rationalBCHClass_eq_top hLow]
  congr 1
  apply evaluatedTopComponent_eq_of_sub_order_two
  intro i
  unfold bchPair
  split
  · exact ha
  · exact hc

/-- BCH associativity induces Eichler's cocycle identity on the rational
Lie obstruction quotient (BB (9.81), p. 472). -/
theorem rationalBCHClass_cocycle {b n : ℕ} {p : Fin b → ℕ+} (hn : 3 ≤ n)
    (hLow : ∀ j < n, bchComponent j ∈ rationalSeriesLieAlgebra 2)
    (a c d : rationalCoefficientLieAlgebra b n p) :
    rationalBCHClass (a + c) d + rationalBCHClass a c =
      rationalBCHClass a (c + d) + rationalBCHClass c d := by
  let π := rationalLieQuotientMap b n p
  have ha := rationalCoefficientLieAlgebra_positive a.property
  have hc := rationalCoefficientLieAlgebra_positive c.property
  have hd := rationalCoefficientLieAlgebra_positive d.property
  let t : rationalCoefficientLieAlgebra b n p :=
    ⟨finiteBCHLowerPart a.val c.val ha hc,
      finiteBCHLowerPart_mem_rationalLieAlgebra hLow _ _ ha hc a.property c.property⟩
  let u : rationalCoefficientLieAlgebra b n p :=
    ⟨finiteBCHLowerPart c.val d.val hc hd,
      finiteBCHLowerPart_mem_rationalLieAlgebra hLow _ _ hc hd c.property d.property⟩
  have ht := rationalCoefficientLieAlgebra_positive t.property
  have hu := rationalCoefficientLieAlgebra_positive u.property
  have htl : rationalBCHClass t d = rationalBCHClass (a + c) d :=
    rationalBCHClass_eq_of_sub_order_two hLow _ _ _ _
      (finiteBCHLowerPart_sub_add_order (by omega) _ _ ha hc)
      (by simpa using finiteOrderAtLeast_zero_element (a := b) (p := p) (s := n) 2)
  have hur : rationalBCHClass a u = rationalBCHClass a (c + d) :=
    rationalBCHClass_eq_of_sub_order_two hLow _ _ _ _
      (by simpa using finiteOrderAtLeast_zero_element (a := b) (p := p) (s := n) 2)
      (finiteBCHLowerPart_sub_add_order (by omega) _ _ hc hd)
  have hl : π (finiteBCH (finiteBCH a.val c.val) d.val) =
      rationalBCHClass (a + c) d + rationalBCHClass a c := by
    rw [finiteBCH_eq_lower_add_top _ _ ha hc]
    rw [finiteBCH_top_shift_left (by omega) ht hd (evaluatedComponent_order _ _ n), map_add]
    change rationalBCHClass t d + _ = _
    rw [htl, rationalBCHClass_eq_top hLow a c]
  have hr : π (finiteBCH a.val (finiteBCH c.val d.val)) =
      rationalBCHClass a (c + d) + rationalBCHClass c d := by
    rw [finiteBCH_eq_lower_add_top _ _ hc hd]
    rw [finiteBCH_top_shift_right (by omega) ha hu (evaluatedComponent_order _ _ n), map_add]
    change rationalBCHClass a u + _ = _
    rw [hur, rationalBCHClass_eq_top hLow c d]
  rw [← hl, ← hr, finiteBCH_assoc ha hc hd]
end RothschildStein.G3
