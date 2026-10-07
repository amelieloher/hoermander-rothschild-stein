-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Joint continuity of the zeroth spatial jet is joint
continuity of the actual field values (BB p. 452). -/
theorem spatial_jet_zero_continuity_values {P E F : Type*}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (f : P → E → F)
    (h : ContinuousOn (fun q : P × E => iteratedFDeriv ℝ 0 (f q.1) q.2) S) :
    ContinuousOn (fun q : P × E => f q.1 q.2) S := by
  have hc := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_continuousOn h
  apply hc.congr
  intro q _hq
  change f q.1 q.2 = (continuousMultilinearCurryFin0 ℝ E F) (iteratedFDeriv ℝ 0 (f q.1) q.2)
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  simp

/-- Joint continuity of a successor spatial jet gives joint
continuity of the corresponding jet of the actual spatial derivative.
No parameter derivative is introduced (BB p. 452). -/
theorem spatial_derivative_jet_continuity {P E F : Type*} (j : ℕ)
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (f : P → E → F)
    (h : ContinuousOn (fun q : P × E => iteratedFDeriv ℝ (j + 1) (f q.1) q.2) S) :
    ContinuousOn (fun q : P × E => iteratedFDeriv ℝ j (fderiv ℝ (f q.1)) q.2) S := by
  have hc := (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp_continuousOn h
  apply hc.congr
  intro q _hq
  change iteratedFDeriv ℝ j (fderiv ℝ (f q.1)) q.2 =
    (continuousMultilinearCurryRightEquiv' ℝ j E F) (iteratedFDeriv ℝ (j + 1) (f q.1) q.2)
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  simp

/-- Subtraction preserves joint continuity of finite actual
spatial jets on a common open domain (BB p. 452). -/
theorem spatial_jet_sub_continuity {P E F : Type*} (j : ℕ)
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set P} {Ω : Set E} (hΩ : IsOpen Ω) (f g : P → E → F)
    (hf : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (f p) Ω)
    (hg : ∀ p ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (g p) Ω)
    (hfj : ContinuousOn (fun q : P × E => iteratedFDeriv ℝ j (f q.1) q.2) (U ×ˢ Ω))
    (hgj : ContinuousOn (fun q : P × E => iteratedFDeriv ℝ j (g q.1) q.2) (U ×ˢ Ω)) :
    ContinuousOn (fun q : P × E =>
      iteratedFDeriv ℝ j (fun x => f q.1 x - g q.1 x) q.2) (U ×ˢ Ω) := by
  apply (hfj.sub hgj).congr
  intro q hq
  exact iteratedFDeriv_sub_apply
    (((hf q.1 hq.1).contDiffAt (hΩ.mem_nhds hq.2)).of_le (by simp))
    (((hg q.1 hq.1).contDiffAt (hΩ.mem_nhds hq.2)).of_le (by simp))

end RothschildStein.G4
