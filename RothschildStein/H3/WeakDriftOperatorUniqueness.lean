-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevOperatorData
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The fixed weak equation identifies the actual drift operator
almost everywhere, by the existing empty-word uniqueness theorem. -/
theorem WeakDriftOperatorData.operator_ae_eq_of_pairing {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u F : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hp : 1 ≤ p) (hF : MemLp F p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x in (Ω : Set (Fin n → ℝ)), F x * ψ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), u x * sumSquaresWithDriftTranspose X ψ x) :
    D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F := by
  have ho := locallyIntegrableOn_of_locallyIntegrable_restrict
    (D.operator_memLp.locallyIntegrable hp)
  have hf := locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable hp)
  have hh : hasWeakWordDeriv X Ω [] D.operator F := by
    refine ⟨ho, hf, fun ψ => ?_⟩
    simpa only [wordTranspose] using (heq ψ).trans (D.operator_pairing hX ψ).symm
  exact S.hasWeakWordDeriv_unique X Ω (S.hasWeakWordDeriv_nil X Ω ho) hh

/-- Weak drift operators are independent of the selected Sobolev jet
representatives up to null sets. -/
theorem WeakDriftOperatorData.operator_ae_eq {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D E : WeakDriftOperatorData X Ω p u)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hp : 1 ≤ p) :
    D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] E.operator :=
  D.operator_ae_eq_of_pairing hX hp E.operator_memLp (E.operator_pairing hX)

end RothschildStein.H3
