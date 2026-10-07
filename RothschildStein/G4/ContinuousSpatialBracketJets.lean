-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousSpatialBilinearJets
public import RothschildStein.G1.BracketAlgebra

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Joint continuity of spatial jets of an actual bracket
consumes one additional primitive spatial jet. External parameters are
only topological (BB p. 452). -/
theorem spatial_jet_lieBracket_continuity {P E : Type*}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} {Ω : Set E} (hΩ : IsOpen Ω) (j : ℕ) (f g : P → E → E)
    (hf : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (f p) Ω)
    (hg : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (g p) Ω)
    (hfj : ∀ i ≤ j + 1, ContinuousOn (fun q : P × E => iteratedFDeriv ℝ i (f q.1) q.2) (U ×ˢ Ω))
    (hgj : ∀ i ≤ j + 1, ContinuousOn (fun q : P × E => iteratedFDeriv ℝ i (g q.1) q.2) (U ×ˢ Ω)) :
    ContinuousOn (fun q : P × E =>
      iteratedFDeriv ℝ j (VectorField.lieBracket ℝ (f q.1) (g q.1)) q.2) (U ×ˢ Ω) := by
  let B : E →L[ℝ] (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E
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
  have h1 := spatial_jet_bilinear_continuity hΩ j B f (fun p => fderiv ℝ (g p)) hf hdg
    (fun i hi => hfj i (Nat.le_succ_of_le hi)) hdgj
  have h2 := spatial_jet_bilinear_continuity hΩ j B g (fun p => fderiv ℝ (f p)) hg hdf
    (fun i hi => hgj i (Nat.le_succ_of_le hi)) hdfj
  exact spatial_jet_sub_continuity j hΩ
    (fun p x => fderiv ℝ (g p) x (f p x))
    (fun p x => fderiv ℝ (f p) x (g p x))
    (fun p hp => (hdg p hp).clm_apply (hf p hp))
    (fun p hp => (hdf p hp).clm_apply (hg p hp)) h1 h2

end RothschildStein.G4
