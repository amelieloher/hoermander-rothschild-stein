-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.BoundedSolverGeometry
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The bounded-domain solver on control balls for the fixed-coefficient
distribution equation, under the global control-norm hypotheses and with
the fundamental kernel (BB Thm. 8.5, p. 340). -/
theorem ballLpSolvability_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields) :
    Provider.BallLpSolvability G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) P.norm := by
  intro p hp hpt R hR
  have hpt' : p ≠ ⊤ := hpt.ne
  have hpReal : 1 < p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt').2 hp
  let hpFact : Fact (1 ≤ p) := ⟨hp.le⟩
  let hpRealFact : Fact (1 ≤ ENNReal.ofReal p.toReal) := ⟨by
    simpa only [ENNReal.ofReal_toReal hpt'] using hp.le⟩
  let r : ℝ≥0∞ := (1-p⁻¹)⁻¹
  let hpr : ENNReal.HolderConjugate p r := ⟨by
    change p⁻¹ + ((1-p⁻¹)⁻¹)⁻¹ = (1 : ℝ≥0∞)⁻¹
    rw [inv_inv, inv_one]
    apply add_tsub_cancel_of_le
    simpa only [inv_one] using (ENNReal.inv_le_inv.mpr hp.le)⟩
  let hprReal : ENNReal.HolderConjugate (ENNReal.ofReal p.toReal) r := by
    simpa only [ENNReal.ofReal_toReal hpt'] using hpr
  let hrFact : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r p⟩
  obtain ⟨A,hA,hbound⟩ := bounded_domain_solver_of_controlNorm G H K hQ P
    P.norm P.constant_one P.symmetric R hR p.toReal hpReal r
  refine ⟨A,hA,?_⟩
  intro Ω hΩ f hf
  have hΩ' : (Ω : Set (Fin N → ℝ)) ⊆ quasiballDomain G P.norm 0 R := by
    intro x hx
    have hd := hΩ hx
    change controlDistance univ driftWeight H.fields 0 x < ENNReal.ofReal R at hd
    rw [P.distance_eq] at hd
    have hd' := (ENNReal.ofReal_lt_ofReal_iff hR).mp hd
    change G2.gaugeDistance G P.norm x 0 < R
    rw [G2.gaugeDistance_symmetric G P.norm P.symmetric 0 x]
    exact hd'
  have hf' : MemLp f (ENNReal.ofReal p.toReal) (volume.restrict (Ω : Set (Fin N → ℝ))) := by
    simpa only [ENNReal.ofReal_toReal hpt'] using hf
  obtain ⟨u,hu,D,hop,hb⟩ := hbound Ω hΩ' f hf'
  have hfloc : LocallyIntegrableOn f (Ω : Set (Fin N → ℝ)) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp.le)
  refine ⟨u,?_,⟨hfloc,?_⟩,?_⟩
  · simpa only [ENNReal.ofReal_toReal hpt'] using hu
  · intro ψ
    have heq := D.ofFun_adjoint_equation (by
      simpa only [ENNReal.ofReal_toReal hpt'] using hp.le)
      (fun i => (H.fields_smooth G i).contDiffOn) f hop ψ
    rw [adjointTest_zero_eq_driftTransposeTest] at heq
    exact heq
  · simpa only [ENNReal.ofReal_toReal hpt'] using hb

end RothschildStein.H3
