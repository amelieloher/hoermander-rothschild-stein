-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ChangeCutoff
public import RothschildStein.G3.BCHTopOrder
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The kernel of lowering the cutoff is exactly the next weighted
filtration layer (BB pp. 419–420). -/
theorem cutoffHom_eq_zero_iff_order {a s k : ℕ} {p : Fin a → ℕ+}
    (hks : k ≤ s) (f : FiniteWordAlgebra a s p) :
    cutoffHom hks f = 0 ↔ FiniteOrderAtLeast (k + 1) f := by
  rw [finiteOrderAtLeast_iff]
  constructor
  · intro hz J hJ
    have hw : wordWeight p J.val ≤ k := by omega
    have hh := congrFun hz (boundedWord p J.val hw)
    exact hh
  · intro hf
    funext J
    exact hf (boundedWord p J.val ((boundedWord_weight J).trans hks))
      (by simpa only [boundedWord, boundedWordList] using Nat.lt_succ_of_le (boundedWord_weight J))

/-- Multiplying by a weight-k correction adds it modulo the next
layer. The correction is central after lowering the cutoff to k
(BB Theorem 9.25, pp. 419–420). -/
theorem finiteBCH_high_layer_sub_add_order {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) {A B : FiniteWordAlgebra a s p}
    (hA : FiniteOrderAtLeast 1 A) (hB : FiniteOrderAtLeast k B) :
    FiniteOrderAtLeast (k + 1) (finiteBCH A B - (A + B)) := by
  apply (cutoffHom_eq_zero_iff_order hks _).mp
  rw [map_sub, map_add, cutoffHom_finiteBCH hks hA (finiteOrderAtLeast_mono hB hk)]
  rw [finiteBCH_eq_add_of_commute (cutoffHom_order hks hA)
    (cutoffHom_order hks (finiteOrderAtLeast_mono hB hk))
    (commute_of_top_order (cutoffHom_order hks hB) (cutoffHom_order hks hA)).symm,
    sub_self]
end RothschildStein.G3
