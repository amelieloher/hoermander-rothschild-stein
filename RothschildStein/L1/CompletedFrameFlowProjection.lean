-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CompletedFrameShiftCoefficients
public import RothschildStein.L1.WordFlowProjection

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- The actual completed lifted flow projects onto the original
shifted chart flow for the corresponding inserted parameters, by ODE
uniqueness on the entire common interval (BB pp. 520–521). -/
theorem completed_frame_flow_projection_eqOn {q n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (α : ℝ → (Fin (n+m) → ℝ)) (β : ℝ → (Fin n → ℝ))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hα : ∀ t ∈ Ioo a b,
      HasDerivAt α (∑ i : Fin (n+m), Fin.append u v i •
        G4.shortField w (triangularLift X P) (Fin.addCases B J i) (α t)) t ∧
        α t ∈ basePoint ⁻¹' Ω)
    (hβ : ∀ t ∈ Ioo a b,
      HasDerivAt β (∑ i : Fin (n+Fintype.card (G4.ShortWord w s)),
        Fin.append u (completionShift w J v) i •
        G4.shortField w X (G4.selectedAuxiliaryIndex w B i) (β t)) t ∧ β t ∈ Ω)
    (heq : basePoint (α t₀) = β t₀) :
    EqOn (fun t => basePoint (α t)) β (Ioo a b) := by
  let IJ : Fin (n+m) → G4.ShortWord w s := Fin.addCases B J
  apply word_flow_projection_eqOn hΩ X hX P
    (fun i : Fin (n+m) => (IJ i).val) (Fin.append u v) α β ht₀ hα _ heq
  intro t ht
  change HasDerivAt β (∑ i : Fin (n+m), Fin.append u v i •
    G4.shortField w X (Fin.addCases B J i) (β t)) t ∧ β t ∈ Ω
  rw [completionShift_field_eq w B J u v (G4.shortField w X) (β t)]
  exact hβ t ht

end RothschildStein.L1
