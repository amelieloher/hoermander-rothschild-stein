-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ConstantWordJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- For a function with zero lower ordinary
jets, an r-fold smooth field product equals its top jet on the field values. -/
theorem wordDerivative_eq_top_jet_on {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : (Fin N → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (q : Fin r → Fin a)
    (hz : ∀ j < r, iteratedFDeriv ℝ j u x = 0) :
    wordDerivative X (List.ofFn q) u x =
      iteratedFDeriv ℝ r u x (fun i => X (q i) x) := by
  have he := iteratedFDeriv_wordDerivative_eq_frozen_on Ω X hX (List.ofFn q) u hu hx 0
    (by simpa using hz)
  have he' := congrArg (fun A => A (Fin.elim0 : Fin 0 → (Fin N → ℝ))) he
  simp only [iteratedFDeriv_zero_apply] at he'
  rw [he']
  exact wordDerivative_constant_eq_iteratedFDeriv Ω (fun i => X i x) u hu hx q

/-- Shorter products preserve the previously
realized prescriptions when a correction has zero lower ordinary jets. -/
theorem wordDerivative_zero_of_lower_jets_on {a N r : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : (Fin N → ℝ) → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (I : List (Fin a)) (hI : I.length < r)
    (hz : ∀ j < r, iteratedFDeriv ℝ j u x = 0) : wordDerivative X I u x = 0 := by
  have he := iteratedFDeriv_wordDerivative_zero_on Ω X hX I u hu hx hz 0 (by simpa using hI)
  simpa only [iteratedFDeriv_zero_apply,zero_apply] using
    congrArg (fun A => A (Fin.elim0 : Fin 0 → (Fin N → ℝ))) he
end RothschildStein.L1
