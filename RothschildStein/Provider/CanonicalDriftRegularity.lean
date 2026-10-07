-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.FundamentalSolutionInputs
public import RothschildStein.H3.GlobalLpRegularityGeometry
public import RothschildStein.H3.CompactHolderEstimatesGeometry
public import RothschildStein.H3.LocalLpRegularityGeometry
public import RothschildStein.H3.BallLpSolvabilityGeometry
public import RothschildStein.H3.QuasiballLpTransfer
public import RothschildStein.H3.LocalHolderRegularityControlNorm
public import RothschildStein.H3.EnlargedGaugeBallSolver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.Provider

/-- Every drift regularity input and both gauge-transfer statements follow
from the hypotheses on the canonical system, with no analytic premises. -/
theorem groupRegularityInputs_canonical_drift {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q + 1 ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hQ : 3 ≤ G.homogeneousDimension)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ))
    (hνs_symm : ∀ x, νs (G.inv x) = νs x) :
    GroupRegularityInputs G driftWeight (G.driftFields hq)
      (fun Ω => hasDistributionEquationWithDrift Ω (G.driftFields hq)
        (fun i => (G.driftFields_contDiff hq i).contDiffOn)) νs := by
  let H := driftStandingHypotheses G hq hqpos hw hw0 hspan νs hνs
  have hQ' : 2 < (G.homogeneousDimension : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 2 < 3) hQ)
  obtain ⟨K⟩ := H.exists_globalFundamentalKernel G hQ'
  let P := H3.standingControlNormConclusion G H
  obtain ⟨E,hE,hE0,hflow⟩ := H.exists_global_horizontal_flows G
  obtain ⟨μ⟩ := G2.nonempty_groupMollifier G H.norm
  obtain ⟨φ⟩ := G2.nonempty_groupMollifier G P.norm
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact H3.globalLpRegularity_of_geometry_and_flow G H K hQ' P E hE hE0 hflow
  · exact H3.compactHolderEstimates_of_controlNorm G H K hQ' P
  · exact H3.localLpRegularity_of_geometry_and_flow G H K hQ' P E hE hE0 hflow
  · exact H3.localHolderRegularity_of_controlNorm G H K hQ' P μ φ νs
  · exact H3.ballLpSolvability_of_controlNorm G H K hQ' P
  · exact H3.quasiballLpTransfer_holds G H K hQ' H.norm hνs_smooth hνs_symm
  · change HolderBallTransfer G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) H.norm
    intro α hα hα1 R hR
    let a : ℝ≥0 := ⟨α, hα.le⟩
    have ha : 0 < a := hα
    obtain ⟨S,hRS,V,hV,hRV,A,hA,hsolve⟩ :=
      H3.enlarged_gauge_ball_solver_of_controlNorm G H K hQ' P φ H.norm ha hα1 hR
    have hball : {x | controlDistance univ driftWeight H.fields 0 x < ENNReal.ofReal R} =
        {x | P.norm x < R} := by
      ext x
      change controlDistance univ driftWeight H.fields 0 x < ENNReal.ofReal R ↔ P.norm x < R
      rw [P.distance_eq]
      rw [ENNReal.ofReal_lt_ofReal_iff hR]
      change P.norm (G.mul (G.inv x) 0) < R ↔ _
      rw [G2.mul_zero, P.symmetric]
    refine ⟨S,hRS,V,hV,?_,A,hA,?_⟩
    · simpa only [hball] using hRV
    · intro Ω hΩ f hf hz
      exact hsolve Ω (by simpa only [hball] using hΩ) f hf hz

/-- The seven canonical drift input families hold. -/
theorem canonicalDriftRegularity_holds : CanonicalDriftRegularity := by
  constructor
  all_goals
    intro N q G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm
    have h := groupRegularityInputs_canonical_drift G hq hqpos hw hw0 hQ hspan νs hνs hνs_smooth hνs_symm
  · exact h.globalLp
  · exact h.compactHolder
  · exact h.localLp
  · exact h.localHolder
  · exact h.lpSolve
  · exact h.quasiball
  · exact h.holderBall

end RothschildStein.Provider
