-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ControlledTriangularLift
public import RothschildStein.P1.PaddingCoordinates

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.L1

/-- Ambient balls of the actual triangular lift project exactly
onto the original balls. No confinement to the small free patch is assumed
for the arbitrary connecting curves used in this statement. -/
theorem rsBall_triangularLift_projection_eq {q n m : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hP : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n + l.val)
    (ξ : Fin (n + m) → ℝ) (r : ℝ) :
    basePoint '' rsBall (basePoint ⁻¹' Ω) w (triangularLift X P) ξ r =
      rsBall Ω w X (basePoint ξ) r := by
  apply Subset.antisymm (rsBall_triangularLift_projection hΩ w X P ξ r)
  intro y hy
  obtain ⟨δ, hδ, hδr, γ, hγ, hγ0, hγ1⟩ :=
    G1.exists_controlledCurve_of_controlDistance_lt hy.2
  obtain ⟨η, hη, hη0, hproj⟩ := exists_controlled_triangularLift w X P hP hγ
    (P1.paddingFiberCLM n m ξ)
  have hstart : η 0 = ξ := by
    rw [hη0, hγ0]
    simpa only [P1.paddingJoinCLM_apply, P1.paddingBaseCLM_apply] using
      P1.paddingJoinCLM_projections n m ξ
  refine ⟨η 1, ⟨hη.2.2.1 (by norm_num), ?_⟩, ?_⟩
  · have hcost := G1.controlDistance_le_of_curve hη
    rw [hstart] at hcost
    exact hcost.trans_lt (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hδr, hδ.trans hδr⟩)
  · rw [hproj, hγ1]

end RothschildStein.L1
