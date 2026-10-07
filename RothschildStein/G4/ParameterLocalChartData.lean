-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SpatialChartData
public import RothschildStein.G4.ParameterShiftedChartWithJacobian
public import RothschildStein.G4.ParameterLocalBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators Topology
namespace RothschildStein.G4

/-- Construct the full compact-parameter chart family near every
spatial point, deriving finite budgets from joint spatial jets (BB p. 452). -/
theorem exists_parameter_local_chart_data {P : Type*}
    [UniformSpace P] [CompactSpace P] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : P → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ p j, ContDiffOn ℝ (⊤ : ℕ∞) (X p j) Ω)
    (hstep : ∀ p, bracketStepOn Ω w (X p) s)
    (hjoint : ∀ J, ∀ i ≤ max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)),
      ContinuousOn (fun z : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2)
        (univ ×ˢ Ω))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun J => shortWeight w (shortIndex w J)
    let Zf := fun p J => shortField w (X p) (shortIndex w J)
    ∃ A : SpatialChartData Ω wf Zf t, z ∈ A.U := by
  classical
  intro m wf Zf
  let H := max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s))
  have hH : s+1 ≤ H := by dsimp [H]; omega
  obtain ⟨R, Δ, M, hR, hΔ, hM, hRΩ, hjets, hmax⟩ :=
    exists_parameter_local_buffer hΩ w X hX hstep H hH hjoint hz
  have hj : ∀ J, ∀ i ≤ s+1, ContinuousOn
      (fun z : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2) (univ ×ˢ Ω) :=
    fun J i hi => hjoint J i (hi.trans hH)
  let δ := R / (64 * (1 + ((n+m : ℕ) : ℝ) * wordJetBase n 0 s M ^ s))
  have hδ : 0 < δ := by
    have hb := (wordJetBase_nonneg_and_le hM.le (n := n) (h := 0) (l := s)).1
    dsimp [δ]
    positivity
  have hKball : closedBall z (R/16) ⊆ ball z (R/8) :=
    closedBall_subset_ball (by linarith)
  obtain ⟨Φ, D, κ, r₀, c, hD, hκ, hκs, hr, hr1, hc, hc1, hflow, hchart⟩ :=
    exists_parameter_shifted_chart_with_jacobian k n s h q hn hs horder hq w M Δ R
      hM.le hΔ hR Ω hΩ X hX hstep hj z hRΩ hjets hmax
      (closedBall z (R/16)) (isCompact_closedBall _ _) hKball t ht ht1
  let U := ball z (R/16)
  have hU : U ⊆ ball z (R/4) := ball_subset_ball (by linarith)
  have hUΩ : U ⊆ Ω :=
    ((ball_subset_ball (by linarith : R/16 ≤ R)).trans ball_subset_closedBall).trans hRΩ
  have hindices : ∀ B : Fin n → Fin m, ∀ j : Fin (n+m),
      selectedAuxiliaryIndex w (shortIndex w ∘ B) j = shortIndex w (Fin.addCases B id j) := by
    intro B j
    have hBf : (Fintype.equivFin (ShortWord w s)) ∘ (shortIndex w ∘ B) = B := by
      funext i
      simp [shortIndex]
    simpa only [hBf] using
      (shortIndex_selectedAuxiliaryIndex w (shortIndex w ∘ B) j).symm
  refine ⟨{
    U := U, isOpen_U := isOpen_ball, subset_domain := hUΩ,
    δ := δ, δ_pos := hδ, c := c, r₀ := r₀, D := D, κ := κ,
    c_pos := hc, c_le_one := hc1, radius_pos := hr, radius_le_one := hr1,
    D_pos := hD, κ_pos := hκ, κ_small := hκs, Φ := Φ,
    smooth := fun p B => (hflow p B).1.mono
      (Set.prod_mono (Set.prod_mono Subset.rfl hU) Subset.rfl),
    flow := ?_, charts := ?_ }, ?_⟩
  · intro p B a ha x hx
    have hf := (hflow p B).2 a ha x (hU hx)
    refine ⟨hf.1, ?_⟩
    intro τ hτ
    have hh := hf.2 τ hτ
    exact ⟨hRΩ (ball_subset_closedBall hh.1), by simpa only [hindices, Zf] using hh.2⟩
  · intro p x hx
    exact hchart p x (ball_subset_closedBall hx)
  · exact mem_ball_self (by positivity)

end RothschildStein.G4
