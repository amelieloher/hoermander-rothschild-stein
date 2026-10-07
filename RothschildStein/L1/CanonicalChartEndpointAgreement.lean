-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalEndpointUniqueness
public import RothschildStein.G4.ChartAnalyticData
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.L1.CanonicalFrameChartData

/-- Actual unshifted ball-box trajectories and the canonical frame flow
have the same endpoint. No endpoint or chart equality is presumed. -/
theorem exists_chart_endpoint_agreement {N : ℕ}
    {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)}
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    {x : Fin N → ℝ} (C : CanonicalFrameChartData Ω Y x)
    (w : Fin N → ℕ+) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ η ∈ ball x (C.radius/2), ∀ u : Fin N → ℝ,
      (C.time⁻¹ • u,η) ∈ ball (0,x) C.initialRadius →
      (∀ i, |u i| ≤ δ^(w i : ℕ)) →
      ∀ (m : ℕ) (Z : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
        (B : Fin N → Fin m), (∀ i, Z (B i) = Y i) →
      ∀ (F : (Fin N → ℝ) → (Fin N → ℝ)) (Q : Set (Fin N → ℝ))
        (Γ : (Fin N → ℝ) → ℝ → (Fin N → ℝ)),
      G4.ChartTrajectories Ω Z B F Q η 0 Γ → u ∈ Q →
      F u = canonicalFrameMap C.time C.flow (η,u) := by
  obtain ⟨ε,hε,he⟩ := C.exists_constant_endpoint_uniqueness hY w
  refine ⟨ε,hε,?_⟩
  intro δ hδ hδε η hη u hq hb m Z B hB F Q Γ hΓ hu
  obtain ⟨hac,hmap,hzero,hone,hd⟩ := hΓ u hu
  have hd' : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt (Γ u) (∑ i, u i • Y i (Γ u t)) t := by
    filter_upwards [hd] with t ht
    have hs : (∑ j : Fin (N+m), Fin.append u 0 j •
        Z (Fin.addCases B id j) (Γ u t)) = ∑ i, u i • Y i (Γ u t) := by
      rw [Fin.sum_univ_add]
      simp [hB]
    exact hs ▸ ht
  exact hone.symm.trans (he δ hδ hδε η hη u hq hb (Γ u) hac hmap hzero hd')
end RothschildStein.L1.CanonicalFrameChartData
