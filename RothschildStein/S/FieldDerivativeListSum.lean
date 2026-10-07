-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Transposes
public import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Function
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {α : Type*}

/-- Differentiability of a finite list sum retains duplicate
kernel terms from the commutator recursion (BB pp. 77–79). -/
theorem differentiableAt_listSum (l : List α) (f : α → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (hf : ∀ a ∈ l, DifferentiableAt ℝ (f a) x) :
    DifferentiableAt ℝ (fun y => (l.map (fun a => f a y)).sum) x := by
  induction l with
  | nil => exact differentiableAt_const 0
  | cons a l ih =>
    simpa only [List.map_cons,List.sum_cons] using!
      (hf a (List.mem_cons_self)).add (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

/-- A classical field derivative distributes over the recursive
finite list sum, with all differentiability hypotheses discharged for
smooth kernel terms at the application (BB pp. 77–79). -/
theorem fieldDerivative_listSum (V : (Fin n → ℝ) → (Fin n → ℝ))
    (l : List α) (f : α → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : ∀ a ∈ l, DifferentiableAt ℝ (f a) x) :
    fieldDerivative V (fun y => (l.map (fun a => f a y)).sum) x =
      (l.map (fun a => fieldDerivative V (f a) x)).sum := by
  induction l with
  | nil => simp only [List.map_nil,List.sum_nil,fieldDerivative,fderiv_const_apply,zero_apply]
  | cons a l ih =>
    have ht : ∀ b ∈ l, DifferentiableAt ℝ (f b) x :=
      fun b hb => hf b (List.mem_cons_of_mem a hb)
    simp only [List.map_cons,List.sum_cons]
    unfold fieldDerivative
    rw [fderiv_fun_add (hf a List.mem_cons_self) (differentiableAt_listSum l f x ht)]
    change _ + fieldDerivative V (fun y => (l.map (fun a => f a y)).sum) x = _
    rw [ih ht]
    rfl

end RothschildStein.S
