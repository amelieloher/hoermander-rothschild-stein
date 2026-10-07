-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialGaugeProducts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Products of homogeneous gauge derivatives retain exactly
 the degree 'number of factors minus total word weight'. -/
theorem radialGaugeProduct_abs_bound {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (ν : (Fin n → ℝ) → ℝ)
    (w : Fin m → ℕ+) (M : List (Fin m) → ℝ) (Ks : List (List (Fin m)))
    (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hM : ∀ K ∈ Ks, 0 ≤ M K)
    (hb : ∀ K ∈ Ks, |wordDerivative X K ν x| ≤ M K * r ^ (1-(wordWeight w K : ℝ))) :
    |radialGaugeProduct X ν Ks x| ≤ (Ks.map M).prod *
      r ^ ((Ks.length : ℝ)-((Ks.map (wordWeight w)).sum : ℝ)) := by
  induction Ks with
  | nil => simp [radialGaugeProduct]
  | cons K Ks ih =>
    have hmK := hM K (List.mem_cons_self ..)
    have hbK := hb K (List.mem_cons_self ..)
    have hMt := fun L hL => hM L (List.mem_cons_of_mem _ hL)
    have hbt := fun L hL => hb L (List.mem_cons_of_mem _ hL)
    have hMtprod : 0 ≤ (Ks.map M).prod := List.prod_nonneg (by
      intro a ha
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
      exact hMt L hL)
    calc
      |radialGaugeProduct X ν (K::Ks) x| =
          |wordDerivative X K ν x| * |radialGaugeProduct X ν Ks x| := by
        rw [radialGaugeProduct,abs_mul]
      _ ≤ (M K*r^(1-(wordWeight w K : ℝ))) *
          ((Ks.map M).prod*r^((Ks.length : ℝ)-((Ks.map (wordWeight w)).sum : ℝ))) :=
        mul_le_mul hbK (ih hMt hbt) (abs_nonneg _) (mul_nonneg hmK (Real.rpow_nonneg hr.le _))
      _ = (M K*(Ks.map M).prod)*
          r^((1-(wordWeight w K : ℝ))+((Ks.length : ℝ)-((Ks.map (wordWeight w)).sum : ℝ))) := by
        rw [Real.rpow_add hr]
        ring
      _ = _ := by
        simp only [List.map_cons,List.prod_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        congr 2
        ring

end RothschildStein.H3
