-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterLinearFieldStateBounds
public import RothschildStein.G4.LinearFieldFlowIntegral
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal

namespace RothschildStein.G4

/-- The actual parameter-linear field has a uniform spatial
Lipschitz constant on a convex compact state carrier, obtained from
field-value and first-derivative budgets (BB p. 452). -/
theorem parameter_linear_field_lipschitzOnWith {m n : ℕ}
    {Ω K : Set (Fin n → ℝ)} {C : Set (Fin m → ℝ)} (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) (hC : Convex ℝ C) (hK : Convex ℝ K)
    (Y : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hY : ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Y J) Ω)
    {A D M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hcoef : ∀ a ∈ C, ‖a‖ ≤ A) (hvalue : ∀ y ∈ K, ∀ J, ‖Y J y‖ ≤ M)
    (hder : ∀ y ∈ K, ∀ J, ‖fderiv ℝ (Y J) y‖ ≤ D) :
    let L : ℝ≥0 := ⟨(m : ℝ) * (A * D + M), by positivity⟩
    LipschitzOnWith L
      (fun p : (Fin m → ℝ) × (Fin n → ℝ) => ∑ J, p.1 J • Y J p.2) (C ×ˢ K) := by
  have hs := linear_field_family_contDiffOn Y hY (univ : Set (Fin m → ℝ))
  have hDiff : ∀ p ∈ C ×ˢ K,
      DifferentiableAt ℝ (fun q : (Fin m → ℝ) × (Fin n → ℝ) => ∑ J, q.1 J • Y J q.2) p := by
    intro p hp
    exact (hs.contDiffAt ((isOpen_univ.prod hΩ).mem_nhds ⟨mem_univ _, hKΩ hp.2⟩)).differentiableAt
      (by simp)
  apply (hC.prod hK).lipschitzOnWith_of_nnnorm_fderiv_le hDiff
  intro p hp
  change ‖fderiv ℝ (fun q : (Fin m → ℝ) × (Fin n → ℝ) => ∑ J, q.1 J • Y J q.2) p‖ ≤
    (m : ℝ) * (A * D + M)
  exact norm_parameter_linear_field_state_fderiv_le Y p hA hD hM (hcoef p.1 hp.1)
    (hvalue p.2 hp.2) (hder p.2 hp.2)
    (fun J => ((hY J).contDiffAt (hΩ.mem_nhds (hKΩ hp.2))).differentiableAt (by simp))

end RothschildStein.G4
