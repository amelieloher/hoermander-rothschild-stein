-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousSpatialJetBasics
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
universe u

namespace RothschildStein.G4

/-- A continuous bilinear operation preserves joint continuity
of finite spatial jets. Differentiation is solely in the spatial variable;
the external parameter is only topological (BB p. 452). -/
theorem spatial_jet_bilinear_continuity {P : Type*} {E F G H : Type u}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set P} {Ω : Set E} (hΩ : IsOpen Ω) (j : ℕ)
    (B : F →L[ℝ] G →L[ℝ] H) (f : P → E → F) (g : P → E → G)
    (hf : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (f p) Ω)
    (hg : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (g p) Ω)
    (hfj : ∀ i ≤ j, ContinuousOn (fun q : P × E => iteratedFDeriv ℝ i (f q.1) q.2) (U ×ˢ Ω))
    (hgj : ∀ i ≤ j, ContinuousOn (fun q : P × E => iteratedFDeriv ℝ i (g q.1) q.2) (U ×ˢ Ω)) :
    ContinuousOn (fun q : P × E =>
      iteratedFDeriv ℝ j (fun x => B (f q.1 x) (g q.1 x)) q.2) (U ×ˢ Ω) := by
  induction j generalizing F G H with
  | zero =>
    have hfv := spatial_jet_zero_continuity_values f (hfj 0 le_rfl)
    have hgv := spatial_jet_zero_continuity_values g (hgj 0 le_rfl)
    have hv := (B.continuous.comp_continuousOn hfv).clm_apply hgv
    have hc := (continuousMultilinearCurryFin0 ℝ E H).symm.continuous.comp_continuousOn hv
    apply hc.congr
    intro q _hq
    rfl
  | succ j ih =>
    have hdf : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (f p)) Ω :=
      fun p hp => (hf p hp).fderiv_of_isOpen hΩ (by simp)
    have hdg : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (g p)) Ω :=
      fun p hp => (hg p hp).fderiv_of_isOpen hΩ (by simp)
    have hdfj : ∀ i ≤ j, ContinuousOn (fun q : P × E =>
        iteratedFDeriv ℝ i (fderiv ℝ (f q.1)) q.2) (U ×ˢ Ω) :=
      fun i hi => spatial_derivative_jet_continuity i f (hfj (i + 1) (by omega))
    have hdgj : ∀ i ≤ j, ContinuousOn (fun q : P × E =>
        iteratedFDeriv ℝ i (fderiv ℝ (g q.1)) q.2) (U ×ˢ Ω) :=
      fun i hi => spatial_derivative_jet_continuity i g (hgj (i + 1) (by omega))
    have h1 := ih (B.precompR E) f (fun p => fderiv ℝ (g p)) hf hdg
      (fun i hi => hfj i (Nat.le_succ_of_le hi)) hdgj
    have h2 := ih (B.precompL E) (fun p => fderiv ℝ (f p)) g hdf hg
      hdfj (fun i hi => hgj i (Nat.le_succ_of_le hi))
    let A₁ : P → E → E →L[ℝ] H := fun p x => B.precompR E (f p x) (fderiv ℝ (g p) x)
    let A₂ : P → E → E →L[ℝ] H := fun p x => B.precompL E (fderiv ℝ (f p) x) (g p x)
    have hs1 : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (A₁ p) Ω := fun p hp =>
      (B.precompR E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf p hp) (hdg p hp)
    have hs2 : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (A₂ p) Ω := fun p hp =>
      (B.precompL E).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hdf p hp) (hg p hp)
    have hsum : ContinuousOn (fun q : P × E =>
        iteratedFDeriv ℝ j (fun x => A₁ q.1 x + A₂ q.1 x) q.2) (U ×ˢ Ω) := by
      apply (h1.add h2).congr
      intro q hq
      exact iteratedFDeriv_add_apply
        (((hs1 q.1 hq.1).contDiffAt (hΩ.mem_nhds hq.2)).of_le (by simp))
        (((hs2 q.1 hq.1).contDiffAt (hΩ.mem_nhds hq.2)).of_le (by simp))
    have hactual : ContinuousOn (fun q : P × E =>
        iteratedFDeriv ℝ j (fderiv ℝ (fun x => B (f q.1 x) (g q.1 x))) q.2) (U ×ˢ Ω) := by
      apply hsum.congr
      intro q hq
      have he : fderiv ℝ (fun x => B (f q.1 x) (g q.1 x)) =ᶠ[𝓝 q.2]
          (fun x => A₁ q.1 x + A₂ q.1 x) := by
        filter_upwards [hΩ.mem_nhds hq.2] with x hx
        exact B.fderiv_of_bilinear
          (((hf q.1 hq.1).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
          (((hg q.1 hq.1).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
      exact (he.iteratedFDeriv ℝ j).self_of_nhds
    have hc := (continuousMultilinearCurryRightEquiv' ℝ j E H).symm.continuous.comp_continuousOn hactual
    apply hc.congr
    intro q _hq
    exact iteratedFDeriv_succ_eq_comp_right

end RothschildStein.G4
