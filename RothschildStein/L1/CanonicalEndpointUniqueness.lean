-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalControlledTrajectory
public import RothschildStein.G4.CompactControlledCurveBuffer
public import RothschildStein.G4.ACFlowUniqueness
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.L1.CanonicalFrameChartData

/-- Actual small constant-control endpoints coincide with the canonical
flow endpoint. First exit supplies a common compact Lipschitz buffer. -/
theorem exists_constant_endpoint_uniqueness {N : ℕ}
    {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)}
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    {x : Fin N → ℝ} (C : CanonicalFrameChartData Ω Y x)
    (w : Fin N → ℕ+) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ η ∈ ball x (C.radius/2), ∀ u : Fin N → ℝ,
      (C.time⁻¹ • u,η) ∈ ball (0,x) C.initialRadius →
      (∀ i, |u i| ≤ δ^(w i : ℕ)) →
      ∀ γ : ℝ → (Fin N → ℝ), AbsolutelyContinuousOnInterval γ 0 1 →
      MapsTo γ (Icc 0 1) Ω → γ 0 = η →
      (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
        HasDerivAt γ (∑ i, u i • Y i (γ t)) t) →
      γ 1 = canonicalFrameMap C.time C.flow (η,u) := by
  obtain ⟨ε,hε,hε1,hbuffer⟩ := G4.exists_compact_controlled_curve_buffer
    (Ω := Ω) w Y C.radius_pos
    (fun i => (hY i).continuousOn.mono C.closedPatch_subset)
  refine ⟨ε,hε,?_⟩
  intro δ hδ hδε η hη u hq hb γ hac hγΩ hzero hd
  obtain ⟨ψ,hψac,hψΩ,hψzero,hψone,hψd⟩ :=
    C.exists_canonical_controlled_trajectory_of_parameters hq
  have hγc : isControlledCurve Ω w Y δ γ := by
    exact (show G4.IsConstantControlledCurve Ω w Y δ γ from
      ⟨hδ,hac,hγΩ,u,hb,hd⟩).isControlledCurve
  have hψc : isControlledCurve Ω w Y δ ψ := by
    apply G4.IsConstantControlledCurve.isControlledCurve
    refine ⟨hδ,hψac,hψΩ,u,hb,?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hψd t ht
  have hγS := hbuffer δ hδε γ hγc (by rw [hzero]; exact ball_subset_closedBall hη)
  have hψS := hbuffer δ hδε ψ hψc (by rw [hψzero]; exact ball_subset_closedBall hη)
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∑ i, u i • Y i y) Ω :=
    ContDiffOn.sum (fun i _ => (hY i).const_smul (u i))
  obtain ⟨K,hK⟩ := (hc.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).mono
    C.closedPatch_subset |>.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall x C.radius) (isCompact_closedBall x C.radius)
  have he := G4.ac_integralCurve_eqOn hK (hc.continuousOn.mono C.closedPatch_subset)
    hac hγS hd
    (by simpa only [uIcc_of_le zero_le_one] using hψac.continuousOn)
    hψS (fun t ht => hψd t ⟨ht.1,ht.2.le⟩) (hzero.trans hψzero.symm)
  exact (he ⟨zero_le_one,le_rfl⟩).trans hψone
end RothschildStein.L1.CanonicalFrameChartData
