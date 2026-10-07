-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LayerResidual
public import RothschildStein.G3.QuasiRootBounds
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Finite BCH product of a chosen correction list, in pullback
order (BB Theorem 9.25, pp. 419–420). -/
def correctionProduct {a s : ℕ} {p : Fin a → ℕ+} :
    List (FiniteWordAlgebra a s p) → FiniteWordAlgebra a s p
  | [] => 0
  | A :: AS => finiteBCH A (correctionProduct AS)

/-- The BCH product of weight-k corrections still starts at weight k
(BB Theorem 9.25, pp. 419–420). -/
theorem finiteBCH_high_layer_order {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) {A B : FiniteWordAlgebra a s p}
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast k B) :
    FiniteOrderAtLeast k (finiteBCH A B) := by
  have hh := finiteBCH_high_layer_sub_add_order hk hks (finiteOrderAtLeast_mono hA hk) hB
  have he : finiteBCH A B = (finiteBCH A B - (A + B)) + (A + B) := by abel
  rw [he]
  exact finiteOrderAtLeast_add (finiteOrderAtLeast_mono hh (Nat.le_succ k))
    (finiteOrderAtLeast_add hA hB)

/-- A finite product of corrections agrees with their sum through
weight k. Noncommutativity affects only higher layers (BB pp. 419–420). -/
theorem correctionProduct_leading_sum {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) (AS : List (FiniteWordAlgebra a s p))
    (hAS : ∀ A ∈ AS, FiniteOrderAtLeast k A) :
    FiniteOrderAtLeast k (correctionProduct AS) ∧
      FiniteOrderAtLeast (k + 1) (correctionProduct AS - AS.sum) := by
  induction AS with
  | nil =>
    exact ⟨finiteOrderAtLeast_zero_element _, by
      simp only [correctionProduct, List.sum_nil, sub_self]
      exact finiteOrderAtLeast_zero_element _⟩
  | cons A AS ih =>
    have hA := hAS A (List.mem_cons_self ..)
    have ht := ih (fun B hB => hAS B (List.mem_cons_of_mem A hB))
    refine ⟨finiteBCH_high_layer_order hk hks hA ht.1, ?_⟩
    have he : correctionProduct (A :: AS) - (A :: AS).sum =
        (finiteBCH A (correctionProduct AS) - (A + correctionProduct AS)) +
          (correctionProduct AS - AS.sum) := by
      simp only [correctionProduct, List.sum_cons]
      abel
    rw [he]
    exact finiteOrderAtLeast_add
      (finiteBCH_high_layer_sub_add_order hk hks (finiteOrderAtLeast_mono hA hk) ht.1) ht.2
end RothschildStein.G3
