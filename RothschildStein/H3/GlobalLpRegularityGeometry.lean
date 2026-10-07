-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalRegularityFlowGeometry
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Global regularity for representing distributions at every finite
exponent under the geometric and global-flow hypotheses (BB Thm. 8.27,
pp. 360–362). -/
theorem globalLpRegularity_of_geometry_and_flow {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    (E : Fin q → ℝ → (Fin N → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ)) :
    Provider.GlobalLpRegularity G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) P.norm := by
  intro p hp hpt
  have hpt' : p ≠ ⊤ := hpt.ne
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt').2 hp
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  let r : ℝ≥0∞ := (1-p⁻¹)⁻¹
  let hpr : ENNReal.HolderConjugate p r := ⟨by
    change p⁻¹ + ((1-p⁻¹)⁻¹)⁻¹ = (1 : ℝ≥0∞)⁻¹
    rw [inv_inv, inv_one]
    apply add_tsub_cancel_of_le
    simpa only [inv_one] using (ENNReal.inv_le_inv.mpr hp.le)⟩
  let hrFact : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r p⟩
  obtain ⟨C,hC,hbound⟩ := exists_global_regularity_constant_of_geometry_flow G H K hQ P
    P.norm P.constant_one P.symmetric p r hpt' hpReal E hE hE0 hflow
  refine ⟨C,hC,?_⟩
  intro u f hu hf heq
  obtain ⟨T,hTu,hTf⟩ := heq
  rw [hTu.2] at hTf
  obtain ⟨hSob,hsecond,hfull,hfirst⟩ := hbound u f hu hf hTf
  refine ⟨hSob,?_,?_,?_⟩
  · exact hsecond
  · simpa only [add_comm] using hfull
  · simpa only [add_comm] using hfirst

end RothschildStein.H3
