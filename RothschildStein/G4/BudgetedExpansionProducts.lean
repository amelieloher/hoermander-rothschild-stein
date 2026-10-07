-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedExpansionOperations

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

variable {ι : Type*} {n : ℕ} {Ω K : Set (Fin n → ℝ)}
  {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
  {a b h : ℕ} {p q : ℤ} {f g : (Fin n → ℝ) → ℝ} {C D : ℝ}

/-- Multiplying by a generator adds factor counts and deficits
without changing the smooth coefficient budget. -/
theorem budgetedExpansion_mul_generator
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C)
    (hg : IsGenerator Z w B b q g) :
    HasBudgetedGeneratorExpansion Ω K Z w B (a + b) (p + q) h
      (fun x => f x * g x) C := by
  induction hf with
  | zero => exact HasBudgetedGeneratorExpansion.zero.congr (fun x _ => zero_mul _)
  | term d f C hC hd hdC hgen =>
    exact (HasBudgetedGeneratorExpansion.term d (fun x => f x * g x) C hC hd hdC
      (generator_mul hgen hg)).congr (fun x _ => mul_assoc _ _ _)
  | add hf hf' ihf ihf' =>
    exact (HasBudgetedGeneratorExpansion.add ihf ihf').congr (fun x _ => add_mul _ _ _)
  | enlarge hf hCD ih => exact ih.enlarge hCD
  | congr hf heq ih => exact ih.congr (fun x hx => congrArg (fun z => z * g x) (heq hx))

/-- Products of budgeted expansions have an explicit universal
coefficient-jet budget, with no compact-family choice. -/
theorem budgetedExpansion_mul (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C)
    (hg : HasBudgetedGeneratorExpansion Ω K Z w B b q h g D) :
    HasBudgetedGeneratorExpansion Ω K Z w B (a + b) (p + q) h
      (fun x => f x * g x) (scalarJetMultiplier h * C * D) := by
  induction hf with
  | zero =>
    simpa only [mul_zero, zero_mul] using (HasBudgetedGeneratorExpansion.zero
      (Ω := Ω) (K := K) (Z := Z) (w := w) (B := B) (a := a + b) (p := p + q) (h := h))
  | term d f C hC hd hdC hgen =>
    have hb := budgetedExpansion_smooth_mul hΩ hKΩ hd hC hdC
      (budgetedExpansion_mul_generator hg hgen)
    have hb' := hb.congr (g := fun x => (d x * f x) * g x) (fun x _ => by ring)
    simpa only [Nat.add_comm b a, add_comm q p] using hb' 
  | @add f f' C C' hf hf' ihf ihf' =>
    have hb := (HasBudgetedGeneratorExpansion.add ihf ihf').congr
      (g := fun x => (f x + f' x) * g x) (fun x _ => add_mul _ _ _)
    convert hb using 1
    ring
  | enlarge hf hCD ih =>
    exact ih.enlarge (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCD (scalarJetMultiplier_nonneg h))
      (budgetedGeneratorExpansion_nonneg hg))
  | congr hf heq ih => exact ih.congr (fun x hx => congrArg (fun z => z * g x) (heq hx))

end RothschildStein.G4
