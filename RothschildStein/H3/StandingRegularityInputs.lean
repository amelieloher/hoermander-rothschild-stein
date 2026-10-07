-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.StandingLpInterfaces
public import RothschildStein.H3.StandingHolderInterfaces
public import RothschildStein.H3.StandingQuasiballInterface
public import RothschildStein.H3.ZeroDriftLpInterfaces
public import RothschildStein.H3.ZeroDriftCompactHolderInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3

/-- The complete separate shared regularity inputs for a standing
frame, built from the actual H1 kernel and the proved G2/H3 theorems. -/
theorem groupRegularityInputs_standing {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (νs : (Fin N → ℝ) → ℝ) (hνs : G.IsHomogeneousGauge νs)
    (hνs_smooth : ContDiffOn ℝ (⊤ : ℕ∞) νs ({0}ᶜ)) :
    Provider.GroupRegularityInputs G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) νs :=
  ⟨globalLpRegularity_standing G H K hQ νs, compactHolderEstimates_standing G H K hQ νs,
    localLpRegularity_standing G H K hQ νs, localHolderRegularity_standing G H K hQ νs,
    ballLpSolvability_standing G H K hQ νs,
    quasiballLpTransfer_standing G H K hQ νs hνs hνs_smooth,
    holderBallTransfer_standing G H K hQ νs hνs⟩

/-- Transport each of the seven separate regularity conclusions
to the original no-drift frame. The full fixed operators, distances
and function spaces are preserved by the proved zero-channel bridges. -/
theorem groupRegularityInputs_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (D : S.DistanceGeometry (⊤ : Opens (Fin N → ℝ)))
    (hD : D.d = controlDistance univ noDriftWeight X)
    (hnode : Provider.GroupRegularityInputs G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.GroupRegularityInputs G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs :=
  ⟨globalLpRegularity_zero_drift G X hX νs hnode.globalLp,
    compactHolderEstimates_zero_drift G X hX νs D hD hnode.compactHolder,
    localLpRegularity_zero_drift G X hX νs hnode.localLp,
    localHolderRegularity_zero_drift G X hX νs D hD hnode.localHolder,
    ballLpSolvability_zero_drift G X hX νs hnode.lpSolve,
    quasiballLpTransfer_zero_drift G X hX νs hnode.quasiball,
    holderBallTransfer_zero_drift G X hX νs hnode.holderBall⟩

end RothschildStein.H3
