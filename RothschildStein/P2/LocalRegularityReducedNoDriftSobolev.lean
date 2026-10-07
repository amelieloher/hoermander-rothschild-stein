-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedNoDrift
public import RothschildStein.P2.LocalRegularityRootNoDriftSobolev

/-!
# Local regularity without drift, `L^p` (BB Thm 11.1): the root reduced to the P1 hypotheses

`rs3_no_drift_sobolev_of_reducedHypotheses` concludes the statement of
`RothschildStein.rs3_no_drift_sobolev` from `LiftApproximationNoDriftStatement` (the lifting theorem conclusion) and the
two P1 hypotheses `DifferentiationTransferAllChartsNoDrift` (the type-calculus Props `LeftDifferentiation`, `RightDifferentiation`,
`DerivativeTransfer` of the standard frames of the no-drift charts; `TypeKernelIntegrable` is proved) and
`ParametrixErrorTypesAllChartsNoDrift` (`ParametrixErrorTypes` without drift). Nothing else is assumed: the upstream bundle
`NoDriftSobolevHypotheses` of `rs3_no_drift_sobolev_of_hypotheses` is assembled from these
(`leftDifferentiationAllChartsNoDrift_of_differentiationTransfer`, `higherSobolevRegularityNoDrift_of_reducedHypotheses`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- BB Thm 11.1 (no drift, all `k`, `L^p`): the statement of
`RothschildStein.rs3_no_drift_sobolev`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsNoDrift`) and the parametrix error types
(`ParametrixErrorTypesAllChartsNoDrift`); the row integrability is proved
(`LiftedChart.IsStandardFrame.typeKernelIntegrable`). -/
theorem rs3_no_drift_sobolev_of_reducedHypotheses (liftApproximation : LiftApproximationNoDriftStatement)
    (hP : DifferentiationTransferAllChartsNoDrift) (hE : ParametrixErrorTypesAllChartsNoDrift)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (k : ℕ)
    (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX noDriftWeight X Ω k p f →
        hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc noDriftWeight X Ω (k + 2) p u ∧
          sobolevXENorm noDriftWeight X V (k + 2) p u ≤
            ENNReal.ofReal C *
              (sobolevXENorm noDriftWeight X W k p f +
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) :=
  rs3_no_drift_sobolev_of_hypotheses
    ⟨liftApproximation, leftDifferentiationAllChartsNoDrift_of_differentiationTransfer hP, higherSobolevRegularityNoDrift_of_reducedHypotheses liftApproximation hP hE⟩ hn hq Ω V W hV
    hVW hW hWΩ X hX hspan k p hp hp_top

end RothschildStein.P2
