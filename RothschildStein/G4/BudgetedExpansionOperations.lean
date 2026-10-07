-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedGeneratorExpansion
public import RothschildStein.G4.ScalarJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

variable {ι : Type*} {n : ℕ} {Ω K : Set (Fin n → ℝ)}
  {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
  {a b h k : ℕ} {p q : ℤ} {f g d : (Fin n → ℝ) → ℝ} {C D : ℝ}

/-- Relaxing the generator type or requested jet order preserves
its explicit coefficient budget. -/
theorem budgetedExpansion_mono (hab : a ≤ b) (hqp : q ≤ p) (hkh : k ≤ h)
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) :
    HasBudgetedGeneratorExpansion Ω K Z w B b q k f C := by
  induction hf with
  | zero => exact .zero
  | term d g C hC hd hdC hg => exact .term d g C hC hd (hdC.mono hkh) (generator_mono hab hqp hg)
  | add hf hg ihf ihg => exact .add ihf ihg
  | enlarge hf hCD ih => exact .enlarge ih hCD
  | congr hf heq ih => exact .congr ih heq

/-- A generator has the unit coefficient budget at every order. -/
theorem budgetedExpansion_generator (hg : IsGenerator Z w B a p g) :
    HasBudgetedGeneratorExpansion Ω K Z w B a p h g 1 :=
  (HasBudgetedGeneratorExpansion.term (fun _ => 1) g 1 zero_le_one contDiffOn_const
    (one_hasJetBound Ω K h) hg).congr (fun x _ => (one_mul (g x)).symm)

/-- Smooth coefficient multiplication propagates an explicit
finite-jet budget through the expansion. -/
theorem budgetedExpansion_smooth_mul (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) d Ω) (hD : 0 ≤ D) (hdD : HasJetBound Ω K d h D)
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) :
    HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun x => d x * f x)
      (scalarJetMultiplier h * D * C) := by
  induction hf with
  | zero =>
    simpa only [mul_zero] using (HasBudgetedGeneratorExpansion.zero
      (Ω := Ω) (K := K) (Z := Z) (w := w) (B := B) (a := a) (p := p) (h := h))
  | term e g C hC he heC hg =>
    exact (HasBudgetedGeneratorExpansion.term (fun x => d x * e x) g _
      (mul_nonneg (mul_nonneg (scalarJetMultiplier_nonneg h) hD) hC) (hd.mul he)
      (hdD.mul hΩ hKΩ hd he hD hC heC) hg).congr
        (fun x _ => (mul_assoc _ _ _).symm)
  | @add f g C D' hf hg ihf ihg =>
    have hb := (HasBudgetedGeneratorExpansion.add ihf ihg).congr
      (g := fun x => d x * (f x + g x)) (fun x _ => mul_add (d x) _ _)
    convert hb using 1
    ring
  | enlarge hf hCD ih =>
    exact ih.enlarge (mul_le_mul_of_nonneg_left hCD
      (mul_nonneg (scalarJetMultiplier_nonneg h) hD))
  | congr hf heq ih =>
    exact ih.congr (fun x hx => congrArg (fun v => d x * v) (heq hx))

/-- Negating an expansion preserves its explicit coefficient budget. -/
theorem budgetedExpansion_neg (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) :
    HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun x => -f x) C := by
  induction hf with
  | zero => exact HasBudgetedGeneratorExpansion.zero.congr (fun _ _ => neg_zero)
  | term d g C hC hd hdC hg =>
    exact (HasBudgetedGeneratorExpansion.term (fun x => -d x) g C hC hd.neg
      (hdC.neg hΩ hKΩ) hg).congr (fun x _ => (neg_mul (d x) (g x)).symm)
  | add hf hg ihf ihg =>
    exact (HasBudgetedGeneratorExpansion.add ihf ihg).congr (fun x _ => neg_add _ _)
  | enlarge hf hCD ih => exact ih.enlarge hCD
  | congr hf heq ih => exact ih.congr (fun x hx => congrArg Neg.neg (heq hx))

/-- Finite sums add their explicit coefficient budgets. -/
theorem budgetedExpansion_sum {κ : Type*} (S : Finset κ)
    (f : κ → (Fin n → ℝ) → ℝ) (C : κ → ℝ)
    (hf : ∀ j ∈ S, HasBudgetedGeneratorExpansion Ω K Z w B a p h (f j) (C j)) :
    HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun x => ∑ j ∈ S, f j x) (∑ j ∈ S, C j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using
      (HasBudgetedGeneratorExpansion.zero (Ω := Ω) (K := K) (Z := Z) (w := w) (B := B)
        (a := a) (p := p) (h := h))
  | @insert j S hj ih =>
    simpa only [Finset.sum_insert hj] using
      (HasBudgetedGeneratorExpansion.add (hf j (Finset.mem_insert_self _ _))
        (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))))

end RothschildStein.G4
