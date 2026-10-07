-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowDirectionalDerivatives
public import RothschildStein.G4.DirectionalJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Universal bilinear budget for repeated actual flow derivatives. -/
def fieldIterationBudget (h : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => 2 ^ h * fieldIterationBudget (h + 1) j

/-- The iteration budget is nonnegative. -/
theorem fieldIterationBudget_nonneg (h j : ℕ) : 0 ≤ fieldIterationBudget h j := by
  induction j generalizing h with
  | zero => exact zero_le_one
  | succ j ih => exact mul_nonneg (by positivity) (ih (h + 1))

/-- Each actual flow derivative contributes one power of the
vector-field jet budget and consumes one scalar input jet. -/
theorem fieldIterates_jet_bound {n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {T : (Fin n → ℝ) → (Fin n → ℝ)}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T Ω) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (j h : ℕ) {P C : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C)
    (hTP : HasJetBound Ω K T (h + j) P) (hfC : HasJetBound Ω K f (h + j) C) :
    HasJetBound Ω K (fieldIterates T j f) h (fieldIterationBudget h j * C * P ^ j) := by
  induction j generalizing h with
  | zero => simpa only [fieldIterates, fieldIterationBudget, pow_zero, mul_one, one_mul,
      add_zero] using hfC
  | succ j ih =>
    have he : h + (j + 1) = h + 1 + j := by omega
    have hb := ih (h + 1) (by simpa only [he] using hTP) (by simpa only [he] using hfC)
    have hd := HasJetBound.fieldDerivative hΩ hKΩ hT (fieldIterates_contDiffOn hΩ hT hf j)
      hP (mul_nonneg (mul_nonneg (fieldIterationBudget_nonneg _ _) hC) (pow_nonneg hP _))
      (hTP.mono (by omega)) hb
    convert hd using 1
    · rfl
    · simp only [fieldIterationBudget, pow_succ]
      ring

end RothschildStein.G4
