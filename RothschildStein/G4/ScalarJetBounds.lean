-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BracketJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Scalar multiplication of coefficients has an explicit finite
jet multiplier. -/
def scalarJetMultiplier (h : ℕ) : ℝ :=
  ‖(ContinuousLinearMap.mul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ * 2 ^ h

/-- The scalar jet multiplier is nonnegative. -/
theorem scalarJetMultiplier_nonneg (h : ℕ) : 0 ≤ scalarJetMultiplier h :=
  mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (pow_nonneg (by norm_num) _)

/-- Product budgets use the universal scalar Leibniz multiplier. -/
theorem HasJetBound.mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f g : E → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    {h : ℕ} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hfP : HasJetBound Ω K f h P) (hgQ : HasJetBound Ω K g h Q) :
    HasJetBound Ω K (fun x => f x * g x) h (scalarJetMultiplier h * P * Q) :=
  HasJetBound.bilinear hΩ hKΩ (ContinuousLinearMap.mul ℝ ℝ) hf hg hP hQ hfP hgQ

/-- Negating a coefficient preserves its jet budget. -/
theorem HasJetBound.neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f : E → ℝ} {h : ℕ} {P : ℝ} (hf : HasJetBound Ω K f h P) :
    HasJetBound Ω K (fun x => -f x) h P := by
  intro j hj x hx
  change ‖iteratedFDerivWithin ℝ j (-f) Ω x‖ ≤ P
  rw [iteratedFDerivWithin_neg_apply hΩ.uniqueDiffOn (hKΩ hx), norm_neg]
  exact hf j hj x hx

/-- The coefficient one has unit budget at every finite order. -/
theorem one_hasJetBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω K : Set E) (h : ℕ) : HasJetBound Ω K (fun _ : E => (1 : ℝ)) h 1 := by
  intro j hj x hx
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDerivWithin_succ_const]

end RothschildStein.G4
