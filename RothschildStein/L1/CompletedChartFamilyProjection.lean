-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CompletedFrameFlowProjection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- The selected-auxiliary field with zero auxiliary shift is
exactly its selected field, including when the auxiliary carrier is empty. -/
theorem selectedAuxiliaryIndex_zeroShift_field_eq {q d s : ℕ}
    (w : Fin q → ℕ+) (X : Fin q → (Fin d → ℝ) → (Fin d → ℝ))
    (B : Fin d → G4.ShortWord w s) (u : Fin d → ℝ) (x : Fin d → ℝ) :
    (∑ i : Fin (d+Fintype.card (G4.ShortWord w s)),
      Fin.append u (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ) i •
        G4.shortField w X (G4.selectedAuxiliaryIndex w B i) x) =
      ∑ i : Fin d, u i • G4.shortField w X (B i) x := by
  rw [Fin.sum_univ_add]
  simp [G4.selectedAuxiliaryIndex]

/-- The same actual completed and shifted chart families have
identical horizontal endpoints. Whole-interval flow data supply the
identity by uniqueness; no projected-chart identity is an input
(BB pp. 520–521). -/
theorem completed_chart_family_projection {q n m s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (ξ : Fin (n+m) → ℝ) (u : Fin n → ℝ) (v : Fin m → ℝ)
    (Φl : ((Fin (n+m+Fintype.card (G4.ShortWord w s)) → ℝ) ×
      (Fin (n+m) → ℝ)) × ℝ → (Fin (n+m) → ℝ))
    (Φo : ((Fin (n+Fintype.card (G4.ShortWord w s)) → ℝ) ×
      (Fin n → ℝ)) × ℝ → (Fin n → ℝ))
    (hlzero : Φl ((Fin.append (Fin.append u v) 0,ξ),0) = ξ)
    (hozero : Φo ((Fin.append u (completionShift w J v),basePoint ξ),0) = basePoint ξ)
    (hl : ∀ τ ∈ Ioo (-2 : ℝ) 2,
      Φl ((Fin.append (Fin.append u v) 0,ξ),τ) ∈ basePoint ⁻¹' Ω ∧
      HasDerivAt (fun t => Φl ((Fin.append (Fin.append u v) 0,ξ),t))
        (∑ i : Fin (n+m+Fintype.card (G4.ShortWord w s)),
          Fin.append (Fin.append u v) 0 i •
            G4.shortField w (triangularLift X P)
              (G4.selectedAuxiliaryIndex w (Fin.addCases B J) i)
                (Φl ((Fin.append (Fin.append u v) 0,ξ),τ))) τ)
    (ho : ∀ τ ∈ Ioo (-2 : ℝ) 2,
      Φo ((Fin.append u (completionShift w J v),basePoint ξ),τ) ∈ Ω ∧
      HasDerivAt (fun t => Φo ((Fin.append u (completionShift w J v),basePoint ξ),t))
        (∑ i : Fin (n+Fintype.card (G4.ShortWord w s)),
          Fin.append u (completionShift w J v) i •
            G4.shortField w X (G4.selectedAuxiliaryIndex w B i)
              (Φo ((Fin.append u (completionShift w J v),basePoint ξ),τ))) τ) :
    basePoint (Φl ((Fin.append (Fin.append u v) 0,ξ),1)) =
      Φo ((Fin.append u (completionShift w J v),basePoint ξ),1) := by
  have he := completed_frame_flow_projection_eqOn hΩ w X hX P B J u v
    (fun t => Φl ((Fin.append (Fin.append u v) 0,ξ),t))
    (fun t => Φo ((Fin.append u (completionShift w J v),basePoint ξ),t))
    (t₀ := 0) (by constructor <;> norm_num)
    (fun τ hτ => ⟨by simpa only [selectedAuxiliaryIndex_zeroShift_field_eq] using
      (hl τ hτ).2,(hl τ hτ).1⟩)
    (fun τ hτ => ⟨(ho τ hτ).2,(ho τ hτ).1⟩)
    (by rw [hlzero,hozero])
  exact he (by constructor <;> norm_num)

end RothschildStein.L1
