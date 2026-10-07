-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHLayerCorrection
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Exact weight-k coefficient layer in the finite associative
quotient (BB Theorem 9.25, pp. 419–420). -/
def finiteWeightLayer {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ)
    (f : FiniteWordAlgebra a s p) : FiniteWordAlgebra a s p :=
  fun J => if wordWeight p J.val = k then f J else 0

/-- Removing the first possibly nonzero layer raises the weighted
order by one (BB Theorem 9.25, pp. 419–420). -/
theorem sub_weightLayer_order {a s k : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast (k + 1) (f - finiteWeightLayer k f) := by
  rw [finiteOrderAtLeast_iff] at hf ⊢
  intro J hJ
  change f J - (if wordWeight p J.val = k then f J else 0) = 0
  by_cases hk : wordWeight p J.val = k
  · rw [ite_eq_left hk, sub_self]
  · rw [ite_eq_right hk, sub_zero]
    exact hf J (by omega)

/-- A correction matching the leading residual layer reduces the
BCH residual by one weight. This is the exact algebraic induction step,
before quantitative parameter bounds and actual flow comparison. -/
theorem BCH_layer_residual_order {a s k : ℕ} {p : Fin a → ℕ+}
    (hk : 1 ≤ k) (hks : k ≤ s) {T A C : FiniteWordAlgebra a s p}
    (hA : FiniteOrderAtLeast 1 A) (hC : FiniteOrderAtLeast k C)
    (hR : FiniteOrderAtLeast k (T - A))
    (hmatch : FiniteOrderAtLeast (k + 1) (C - finiteWeightLayer k (T - A))) :
    FiniteOrderAtLeast (k + 1) (T - finiteBCH A C) := by
  have hh := finiteBCH_high_layer_sub_add_order hk hks hA hC
  have he : T - finiteBCH A C =
      ((T - A) - finiteWeightLayer k (T - A)) -
        (C - finiteWeightLayer k (T - A)) - (finiteBCH A C - (A + C)) := by abel
  rw [he]
  exact finiteOrderAtLeast_sub (finiteOrderAtLeast_sub (sub_weightLayer_order hR) hmatch) hh
end RothschildStein.G3
