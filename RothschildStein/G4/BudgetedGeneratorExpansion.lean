-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GeneratorExpansion
public import RothschildStein.G4.DirectionalJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Finite generator expansions with an explicit sum of coefficient
jet budgets. Keeping this numerical budget in the induction prevents
compact-family constants from replacing the required finite-jet constants. -/
inductive HasBudgetedGeneratorExpansion {ι : Type*} {n : ℕ}
    (Ω K : Set (Fin n → ℝ)) (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (w : ι → ℕ+) (B : Fin n → ι) (a : ℕ) (p : ℤ) (h : ℕ) :
    ((Fin n → ℝ) → ℝ) → ℝ → Prop
  | zero : HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun _ => 0) 0
  | term (d g : (Fin n → ℝ) → ℝ) (C : ℝ)
      (hC : 0 ≤ C) (hd : ContDiffOn ℝ (⊤ : ℕ∞) d Ω)
      (hdC : HasJetBound Ω K d h C) (hg : IsGenerator Z w B a p g) :
      HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun x => d x * g x) C
  | add {f g : (Fin n → ℝ) → ℝ} {C D : ℝ}
      (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C)
      (hg : HasBudgetedGeneratorExpansion Ω K Z w B a p h g D) :
      HasBudgetedGeneratorExpansion Ω K Z w B a p h (fun x => f x + g x) (C + D)
  | enlarge {f : (Fin n → ℝ) → ℝ} {C D : ℝ}
      (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) (hCD : C ≤ D) :
      HasBudgetedGeneratorExpansion Ω K Z w B a p h f D
  | congr {f g : (Fin n → ℝ) → ℝ} {C : ℝ}
      (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C)
      (heq : EqOn g f (Ω ∩ {x | frameDet Z B x ≠ 0})) :
      HasBudgetedGeneratorExpansion Ω K Z w B a p h g C

/-- Explicit budgets are nonnegative. -/
theorem budgetedGeneratorExpansion_nonneg {ι : Type*} {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    {w : ι → ℕ+} {B : Fin n → ι} {a h : ℕ} {p : ℤ}
    {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) : 0 ≤ C := by
  induction hf with
  | zero => exact le_rfl
  | term d g C hC hd hdC hg => exact hC
  | add hf hg ihf ihg => exact add_nonneg ihf ihg
  | enlarge hf hCD ih => exact ih.trans hCD
  | congr hf heq ih => exact ih

/-- Forgetting the numerical budget gives the previously proved
actual smooth-coefficient expansion class. -/
theorem budgetedGeneratorExpansion_forget {ι : Type*} {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    {w : ι → ℕ+} {B : Fin n → ι} {a h : ℕ} {p : ℤ}
    {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C) :
    HasGeneratorExpansion Ω Z w B a p f := by
  induction hf with
  | zero => exact .zero
  | term d g C hC hd hdC hg => exact .term d g hd hg
  | add hf hg ihf ihg => exact .add ihf ihg
  | enlarge hf hCD ih => exact ih
  | congr hf heq ih => exact .congr ih heq

/-- An explicit coefficient-jet budget yields the exact
suboptimal scale bound with that same budget, without compactness. -/
theorem budgetedGeneratorExpansion_scale_bound {ι : Type*} {n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hKΩ : K ⊆ Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a h : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hf : HasBudgetedGeneratorExpansion Ω K Z w B a p h f C)
    {x : Fin n → ℝ} (hx : x ∈ K) {t r : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hspan : ∃ D : Fin n → ι, frameDet Z D x ≠ 0) (hB : IsSuboptimal Z w B x t r) :
    |f x| ≤ C * t⁻¹ ^ a * r ^ p := by
  induction hf with
  | zero => simp
  | term d g C hC hd hdC hg =>
    have hd₀ : |d x| ≤ C := by simpa using hdC 0 (Nat.zero_le _) x hx
    rw [abs_mul]
    calc
      _ ≤ C * (t⁻¹ ^ a * r ^ p) := mul_le_mul hd₀
        (generator_le_of_suboptimal ht ht1 hr hr1 hspan hB hg) (abs_nonneg _) hC
      _ = _ := by ring
  | add hf hg ihf ihg =>
    exact (abs_add_le _ _).trans ((add_le_add ihf ihg).trans_eq (by ring))
  | enlarge hf hCD ih =>
    exact ih.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (pow_nonneg (inv_nonneg.mpr ht.le) _))
      (zpow_nonneg hr.le _))
  | congr hf heq ih =>
    rw [heq ⟨hKΩ hx, suboptimal_frame_ne_zero ht hr hspan hB⟩]
    exact ih

end RothschildStein.G4
