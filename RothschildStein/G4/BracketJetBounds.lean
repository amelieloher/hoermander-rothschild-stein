-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteJetBounds
public import RothschildStein.G1.BracketAlgebra

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Lowering the requested jet order preserves a budget. -/
theorem HasJetBound.mono {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω K : Set E} {f : E → F}
    {k h : ℕ} {M : ℝ} (hf : HasJetBound Ω K f h M) (hkh : k ≤ h) :
    HasJetBound Ω K f k M := fun j hj x hx => hf j (hj.trans hkh) x hx

/-- Budgets add under subtraction of smooth coefficient maps. -/
theorem HasJetBound.sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω K : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f g : E → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    {h : ℕ} {P Q : ℝ} (hfP : HasJetBound Ω K f h P) (hgQ : HasJetBound Ω K g h Q) :
    HasJetBound Ω K (fun x => f x - g x) h (P + Q) := by
  intro j hj x hx
  change ‖iteratedFDerivWithin ℝ j (f - g) Ω x‖ ≤ P + Q
  rw [iteratedFDerivWithin_sub_apply (hf.of_le (by simp) x (hKΩ hx))
    (hg.of_le (by simp) x (hKΩ hx)) hΩ.uniqueDiffOn (hKΩ hx)]
  exact (norm_sub_le _ _).trans (add_le_add (hfP j hj x hx) (hgQ j hj x hx))

/-- Bracket jets consume precisely one additional coefficient
jet, with an explicit dimension/order polynomial factor
(BB Lemma 9.31, pp. 422–423). -/
theorem HasJetBound.lieBracket {n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {U V : (Fin n → ℝ) → (Fin n → ℝ)}
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    {h : ℕ} {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hUP : HasJetBound Ω K U (h + 1) P) (hVQ : HasJetBound Ω K V (h + 1) Q) :
    HasJetBound Ω K (VectorField.lieBracket ℝ U V) h
      (2 * ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
        (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ * 2 ^ h * P * Q) := by
  let B : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.apply ℝ (Fin n → ℝ)
  have hDUs : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.fderiv ℝ U) Ω := hU.fderiv_of_isOpen hΩ (by simp)
  have hDVs : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.fderiv ℝ V) Ω := hV.fderiv_of_isOpen hΩ (by simp)
  have hfirst := HasJetBound.bilinear hΩ hKΩ B hU hDVs hP hQ
    (hUP.mono (Nat.le_succ h)) (hVQ.fderiv hΩ hKΩ)
  have hsecond := HasJetBound.bilinear hΩ hKΩ B hV hDUs hQ hP
    (hVQ.mono (Nat.le_succ h)) (hUP.fderiv hΩ hKΩ)
  have hh := hfirst.sub hΩ hKΩ (hDVs.clm_apply hU) (hDUs.clm_apply hV) hsecond
  convert hh using 1
  · rfl
  · ring

end RothschildStein.G4
