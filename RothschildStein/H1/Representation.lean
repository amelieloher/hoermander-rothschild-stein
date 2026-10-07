-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.InvariantOperator
public import RothschildStein.G2.TransposeInvariance
public import RothschildStein.G2.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Translating the fundamental pairing gives the representation
formula at every point (BB Theorem 6.20(2), printed pp. 269–270). -/
theorem StandingHypotheses.fundamental_representation
    (H : StandingHypotheses G q) (Γ : (Fin N → ℝ) → ℝ)
    (hfund : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ y, Γ y * sumSquaresWithDriftTranspose H.fields φ y) = φ 0)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (x : Fin N → ℝ) :
    (∫ y, Γ (G.mul (G.inv x) y) * sumSquaresWithDriftTranspose H.fields φ y) = φ x := by
  have ht := hfund (φ ∘ G.mul x) (hφ.comp (G2.contDiff_leftTranslation G x))
    (hc.comp_homeomorph (G2.leftTranslationHomeomorph G x))
  rw [H.transpose_leftInvariant G φ hφ x] at ht
  simp only [Function.comp_apply, G2.mul_zero] at ht
  have hi := G2.integral_leftTranslation G x
    (fun y => Γ (G.mul (G.inv x) y) * sumSquaresWithDriftTranspose H.fields φ y)
  simp only [← G2.mul_assoc, G2.inv_mul, G2.zero_mul] at hi
  exact hi.symm.trans ht

end RothschildStein.H1
