-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ScalarJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Increasing a coefficient budget preserves the bound. -/
theorem HasJetBound.enlarge {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω K : Set E} {f : E → F}
    {h : ℕ} {P Q : ℝ} (hf : HasJetBound Ω K f h P) (hPQ : P ≤ Q) :
    HasJetBound Ω K f h Q := fun j hj x hx => (hf j hj x hx).trans hPQ

/-- Addition sums the coefficient jet budgets. -/
theorem HasJetBound.add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f g : E → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    {h : ℕ} {P Q : ℝ} (hfP : HasJetBound Ω K f h P) (hgQ : HasJetBound Ω K g h Q) :
    HasJetBound Ω K (fun x => f x + g x) h (P + Q) := by
  intro j hj x hx
  change ‖iteratedFDerivWithin ℝ j (f + g) Ω x‖ ≤ P + Q
  rw [iteratedFDerivWithin_add_apply (hf.of_le (by simp) x (hKΩ hx))
    (hg.of_le (by simp) x (hKΩ hx)) hΩ.uniqueDiffOn (hKΩ hx)]
  exact (norm_add_le _ _).trans (add_le_add (hfP j hj x hx) (hgQ j hj x hx))

/-- Constant scalar multiplication uses its exact absolute-value budget. -/
theorem HasJetBound.const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {h : ℕ} {P : ℝ} (hfP : HasJetBound Ω K f h P) (a : ℝ) :
    HasJetBound Ω K (fun x => a * f x) h (|a| * P) := by
  intro j hj x hx
  change ‖iteratedFDerivWithin ℝ j (a • f) Ω x‖ ≤ |a| * P
  rw [iteratedFDerivWithin_const_smul_apply (hf.of_le (by simp) x (hKΩ hx))
    hΩ.uniqueDiffOn (hKΩ hx), norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hfP j hj x hx) (abs_nonneg a)

/-- Constant functions have their absolute-value budget at every order. -/
theorem const_hasJetBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω K : Set E) (h : ℕ) (a : ℝ) : HasJetBound Ω K (fun _ : E => a) h |a| := by
  intro j hj x hx
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDerivWithin_succ_const]

end RothschildStein.G4
