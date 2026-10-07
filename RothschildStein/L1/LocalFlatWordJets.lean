-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LocalFlatFieldJets
public import RothschildStein.S.ClassicalWords
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Ordinary flat jets remain zero after
shorter ordered products, with fields smooth only on the coefficient domain. -/
theorem iteratedFDeriv_wordDerivative_zero_on {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : List (Fin a))
    (u : (Fin N → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hz : ∀ j < r, iteratedFDeriv ℝ j u x = 0) :
    ∀ k, k + I.length < r → iteratedFDeriv ℝ k (wordDerivative X I u) x = 0 := by
  induction I with
  | nil => intro k hk; exact hz k (by simpa using hk)
  | cons i I ih =>
    intro k hk
    apply iteratedFDeriv_fieldDerivative_zero_on (r := r-I.length) Ω (X i)
      (wordDerivative X I u) hx (hX i) (S.contDiffOn_wordDerivative Ω X hX I u hu)
    · intro j hj
      exact ih j (by omega)
    · simp only [List.length_cons] at hk
      omega
end RothschildStein.L1
