-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartPathLift
public import RothschildStein.G4.CoherentPartialLifts
public import RothschildStein.G4.PartialLiftEndpointIdentity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The supremum of actual lift lifetimes is itself a lifetime:
local uniqueness glues the partial lifts, weighted variation constructs
a strictly interior endpoint, and continuity retains the lift identity
(BB Prop 9.52, p. 449). -/
theorem exists_chartPathLift_at_supremum {n s : ℕ} (w : Fin n → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) {a r C b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hCb : 0 ≤ C * b) (hmargin : C * b < (a / 2) ^ s / 4)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    (hF : ContinuousOn F (weightedBox w (a * r)))
    (hlocal : IsLocalHomeomorphOn F (weightedBox w (a * r)))
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (S : Set ℝ) (hS : S.Nonempty) (hS1 : S ⊆ Icc (0 : ℝ) 1)
    (hSup : 0 < sSup S) (θ : S → ℝ → (Fin n → ℝ))
    (hθ : ∀ T : S, IsChartPathLift F γ (θ T) (weightedBox w (a * r)) T)
    (hvariation : ∀ T : S, ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
      |θ T τ i - θ T σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ|) :
    ∃ Θ, IsChartPathLift F γ Θ (weightedBox w (a * r)) (sSup S) := by
  have hSup1 : sSup S ≤ 1 := csSup_le hS (fun T hT => (hS1 hT).2)
  have hcompat : ∀ T₁ T₂ : S, ∀ t ∈ Icc (0 : ℝ) (min (T₁ : ℝ) T₂),
      θ T₁ t = θ T₂ t := by
    intro T₁ T₂
    exact chartPathLift_agree_on_common_prefix F γ (isOpen_weightedBox w (a * r)) hlocal
      (hS1 T₁.property).1 (hS1 T₂.property).1 (hθ T₁) (hθ T₂)
  obtain ⟨χ, hχ0, hχlift, _hχrange, hχvar⟩ :=
    exists_coherent_partialLift_to_supremum w S hS θ F γ (weightedBox w (a * r))
      (fun T => (hθ T).2.1) hcompat (fun T => (hθ T).2.2.2)
      (fun T => (hθ T).2.2.1) hvariation
  obtain ⟨Θ, hΘ, heq, hhalf⟩ := weighted_partialLift_extend_halfBox w hw hr hr1 hSup hSup1
    ha ha1 hCb hmargin χ hχ0 hχvar
  have hΘQ : MapsTo Θ (Icc (0 : ℝ) (sSup S)) (weightedBox w (a * r)) := by
    intro t ht i
    have har : 0 < a * r := mul_pos ha hr
    exact (hhalf t ht i).trans_le
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * r / 2) (by linarith) _)
  have hliftIco : ∀ t ∈ Ico (0 : ℝ) (sSup S), F (Θ t) = γ t := by
    intro t ht
    rw [← heq ht]
    exact hχlift t ht
  have hend : F (Θ (sSup S)) = γ (sSup S) :=
    partialLift_endpoint_identity hSup F Θ γ hΘ.continuous.continuousAt
      ((hF (Θ (sSup S)) (hΘQ ⟨hSup.le, le_rfl⟩)).continuousAt
        ((isOpen_weightedBox w (a * r)).mem_nhds (hΘQ ⟨hSup.le, le_rfl⟩)))
      ((hγ.mono (Icc_subset_Icc le_rfl hSup1)) (sSup S) ⟨hSup.le, le_rfl⟩) hliftIco
  refine ⟨Θ, hΘ.continuous.continuousOn,
    (heq ⟨le_rfl, hSup⟩).symm.trans hχ0, hΘQ, ?_⟩
  intro t ht
  rcases ht.2.eq_or_lt with he | he
  · simpa only [he, Function.comp_apply] using hend
  · exact hliftIco t ⟨ht.1, he⟩

end RothschildStein.G4
