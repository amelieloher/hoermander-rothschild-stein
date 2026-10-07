-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderListSums
public import RothschildStein.S.HolderProducts
public import RothschildStein.S.WordLeibniz
public import Mathlib.Algebra.Order.BigOperators.Group.List

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The Leibniz representative obeys the exact finite
sum-of-products bound in the scalar Hölder norm
(BB p. 84; quantitative Leibniz). -/
theorem holderENorm_leibnizWordValue_le
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) {α : ℝ} (hα : 0 < α)
    (hs : ∀ x ∈ V,∀ y ∈ V,d x y = 0 → x = y)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (a : (Fin n → ℝ) → ℝ)
    (hj : ∀ p ∈ leibnizSplits I,holderENorm d α V (jet p.1) < ⊤)
    (ha : ∀ p ∈ leibnizSplits I,holderENorm d α V (wordDerivative X p.2 a) < ⊤) :
    holderENorm d α V (leibnizWordValue X I jet a) ≤
      ((leibnizSplits I).map (fun p => holderENorm d α V (jet p.1)*
        holderENorm d α V (wordDerivative X p.2 a))).sum := by
  have hp : ∀ p ∈ leibnizSplits I,
      holderENorm d α V (fun x => jet p.1 x*wordDerivative X p.2 a x) ≤
        holderENorm d α V (jet p.1)*holderENorm d α V (wordDerivative X p.2 a) :=
    fun p h => holderENorm_mul_le d hα V hs _ _ (hj p h) (ha p h)
  exact (holderENorm_listSum_le d α V hα hs (leibnizSplits I)
    (fun p x => jet p.1 x*wordDerivative X p.2 a x)
    (fun p h => lt_of_le_of_lt (hp p h) (ENNReal.mul_lt_top (hj p h) (ha p h)))).trans
    (List.sum_le_sum hp)

end RothschildStein.S
