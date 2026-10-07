-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.fieldDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Finite list sums of differentiable functions are differentiable. -/
theorem differentiableAt_list_sum {n : ℕ} {α : Type*} (l : List α)
    (f : α → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : ∀ a ∈ l, DifferentiableAt ℝ (f a) x) :
    DifferentiableAt ℝ (fun y => (l.map (fun a => f a y)).sum) x := by
  induction l with
  | nil => exact differentiableAt_const _
  | cons a l ih =>
    exact (hf a (List.mem_cons_self ..)).add
      (ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)))

/-- Field differentiation commutes with addition of differentiable inputs. -/
theorem fieldDerivative_add_of_differentiable {n : ℕ}
    (V : (Fin n → ℝ) → (Fin n → ℝ)) {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (fun y => f y + g y) x = fieldDerivative V f x + fieldDerivative V g x := by
  have hd : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x := by
    simpa only [Pi.add_def] using fderiv_add hf hg
  simp only [fieldDerivative,hd,add_apply]

/-- Differentiating a finite expansion preserves every repeated term. -/
theorem fieldDerivative_list_sum {n : ℕ} {α : Type*} (l : List α)
    (f : α → (Fin n → ℝ) → ℝ) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (hf : ∀ a ∈ l, DifferentiableAt ℝ (f a) x) :
    fieldDerivative V (fun y => (l.map (fun a => f a y)).sum) x =
      (l.map (fun a => fieldDerivative V (f a) x)).sum := by
  induction l with
  | nil => simp [fieldDerivative]
  | cons a l ih =>
    change fieldDerivative V (fun y => f a y + (l.map (fun b => f b y)).sum) x =
      fieldDerivative V (f a) x + (l.map (fun b => fieldDerivative V (f b) x)).sum
    have hl := fun b hb => hf b (List.mem_cons_of_mem _ hb)
    rw [fieldDerivative_add_of_differentiable (V := V)
      (hf a (List.mem_cons_self ..)) (differentiableAt_list_sum l f x hl),ih hl]

end RothschildStein.H3
