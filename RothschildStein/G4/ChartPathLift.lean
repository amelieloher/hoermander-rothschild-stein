-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalChartLiftUniqueness
public import RothschildStein.G4.PartialLiftContinuation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A continuous partial lift in the prescribed open chart box,
starting at zero. The weighted variation theorem later proves absolute
continuity for these lifts (BB Prop 9.52, p. 449). -/
def IsChartPathLift {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (γ θ : ℝ → (Fin n → ℝ)) (Q : Set (Fin n → ℝ)) (T : ℝ) : Prop :=
  ContinuousOn θ (Icc (0 : ℝ) T) ∧ θ 0 = 0 ∧
    MapsTo θ (Icc (0 : ℝ) T) Q ∧ EqOn (F ∘ θ) γ (Icc (0 : ℝ) T)

/-- The zero-time lift starts the set of lift lifetimes
(BB Prop 9.52, p. 449). -/
theorem chartPathLift_initial {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    {Q : Set (Fin n → ℝ)} (hQ : (0 : Fin n → ℝ) ∈ Q) (hstart : F 0 = γ 0) :
    IsChartPathLift F γ (fun _ => 0) Q 0 := by
  refine ⟨continuousOn_const, rfl, fun _ _ => hQ, ?_⟩
  intro t ht
  have he : t = 0 := le_antisymm ht.2 ht.1
  simpa only [he, Function.comp_apply] using hstart

/-- Partial lifts agree on every common prefix, which supplies
the compatibility used in the supremum construction
(BB Prop 9.52, p. 449). -/
theorem chartPathLift_agree_on_common_prefix {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    {Q : Set (Fin n → ℝ)} (hQ : IsOpen Q) (hF : IsLocalHomeomorphOn F Q)
    {θ₁ θ₂ : ℝ → (Fin n → ℝ)} {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h₁ : IsChartPathLift F γ θ₁ Q T₁) (h₂ : IsChartPathLift F γ θ₂ Q T₂) :
    EqOn θ₁ θ₂ (Icc (0 : ℝ) (min T₁ T₂)) := by
  have hsub₁ : Icc (0 : ℝ) (min T₁ T₂) ⊆ Icc (0 : ℝ) T₁ :=
    Icc_subset_Icc_right (min_le_left _ _)
  have hsub₂ : Icc (0 : ℝ) (min T₁ T₂) ⊆ Icc (0 : ℝ) T₂ :=
    Icc_subset_Icc_right (min_le_right _ _)
  exact local_chart_lift_unique_on hQ F hF (le_min hT₁ hT₂) θ₁ θ₂
    (h₁.1.mono hsub₁) (h₂.1.mono hsub₂)
    (h₁.2.2.1.mono_left hsub₁) (h₂.2.2.1.mono_left hsub₂)
    (fun t ht => (h₁.2.2.2 (hsub₁ ht)).trans (h₂.2.2.2 (hsub₂ ht)).symm)
    (h₁.2.1.trans h₂.2.1.symm)

/-- A partial lift with an actual inverse at its endpoint has a
strictly larger lifetime below time 1 (BB Prop 9.52, p. 449). -/
theorem chartPathLift_extend {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    {Q : Set (Fin n → ℝ)} (hQ : IsOpen Q) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Q)
    (hjac : ∀ u ∈ Q, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {θ : ℝ → (Fin n → ℝ)} {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (hθ : IsChartPathLift F γ θ Q T) :
    ∃ T' : ℝ, T < T' ∧ T' ≤ 1 ∧ ∃ θ', IsChartPathLift F γ θ' Q T' := by
  have ht : T ∈ Icc (0 : ℝ) T := ⟨hT0, le_rfl⟩
  obtain ⟨Ψ, V, hV, hmem, hΨ, hpoint, hmap, hright, _hleft⟩ :=
    exists_actual_inverse_neighborhood hQ F (hθ.2.2.1 ht)
      (hF.contDiffAt (hQ.mem_nhds (hθ.2.2.1 ht))) (hjac (θ T) (hθ.2.2.1 ht))
  have hbase : F (θ T) = γ T := hθ.2.2.2 ht
  have hγT : γ T ∈ V := by rwa [hbase] at hmem
  have hpoint' : Ψ (γ T) = θ T := by rwa [hbase] at hpoint
  obtain ⟨T', hTT', hT'1, θ', hcont, heq, hQ', hlift⟩ :=
    partialLift_extend_of_inverse_patch F Ψ γ θ hV hΨ.continuousOn hmap hright
      hT0 hT1 hγ hγT hpoint' hθ.1 hθ.2.2.1 hθ.2.2.2
  exact ⟨T', hTT', hT'1, θ', hcont,
    (heq ⟨le_rfl, hT0⟩).trans hθ.2.1, hQ', hlift⟩

end RothschildStein.G4
