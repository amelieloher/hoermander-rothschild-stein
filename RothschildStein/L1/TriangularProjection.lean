-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ControlledProjection
public import RothschildStein.Definitions.triangularLift
public import RothschildStein.Definitions.rsBall
public import RothschildStein.P1.PaddingCoordinateDefs

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.L1

/-- The polynomial lift `triangularLift` projects exactly to the original
field, with no restriction on the initial vertical coordinate. -/
theorem basePoint_triangularLift {a n m : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (i : Fin a) (ξ : Fin (n + m) → ℝ) :
    basePoint (triangularLift X P i ξ) = X i (basePoint ξ) := by
  ext j
  simp [basePoint, triangularLift]

/-- Actual curves for the polynomial lift project to
original admissible curves on the original ambient domain. -/
theorem isControlledCurve_triangularLift_projection {a n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    {δ : ℝ} {γ : ℝ → (Fin (n + m) → ℝ)}
    (hγ : isControlledCurve (basePoint ⁻¹' Ω) w (triangularLift X P) δ γ) :
    isControlledCurve Ω w X δ (basePoint ∘ γ) := by
  have hbase : (⇑(P1.paddingBaseCLM n m) : (Fin (n + m) → ℝ) → (Fin n → ℝ)) =
      basePoint := funext (P1.paddingBaseCLM_apply n m)
  have hU : IsOpen (basePoint (n := n) (m := m) ⁻¹' Ω) := by
    simpa only [hbase] using hΩ.preimage (P1.paddingBaseCLM n m).continuous
  simpa only [hbase] using
    isControlledCurve_linear_projection (Ω := Ω) hU (P1.paddingBaseCLM n m)
      (fun ξ hξ => hξ) w X (triangularLift X P)
      (fun ξ _ i => by simpa only [P1.paddingBaseCLM_apply] using basePoint_triangularLift X P i ξ) hγ

/-- Original ambient distance is bounded by the lifted
ambient distance, including nonzero initial vertical coordinates. -/
theorem controlDistance_triangularLift_projection_le {a n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (ξ η : Fin (n + m) → ℝ) :
    controlDistance Ω w X (basePoint ξ) (basePoint η) ≤
      controlDistance (basePoint ⁻¹' Ω) w (triangularLift X P) ξ η := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    G1.controlDistance_le_scaled_transport basePoint (scale := 1) zero_lt_one
      (fun δ γ hγ => by simpa only [one_mul] using
        isControlledCurve_triangularLift_projection hΩ w X P hγ) ξ η

/-- A lifted ambient ball projects inside the original
ambient ball; the zero-fiber assertion follows outside this image. -/
theorem rsBall_triangularLift_projection {a n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin a → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (ξ : Fin (n + m) → ℝ) (r : ℝ) :
    basePoint '' rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r ⊆
      rsBall Ω w X (basePoint ξ) r := by
  rintro z ⟨η, hη, rfl⟩
  exact ⟨hη.1, (controlDistance_triangularLift_projection_le hΩ w X P ξ η).trans_lt hη.2⟩

end RothschildStein.L1
