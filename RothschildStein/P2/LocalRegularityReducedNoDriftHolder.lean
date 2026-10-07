-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedNoDriftHolderLifted
public import RothschildStein.P2.LocalRegularityRootNoDriftHolder

/-!
# Local regularity without drift, Hölder (BB Thm 11.1): the root reduced to the P1 hypotheses

`rs3_no_drift_holder_of_reducedHypotheses` concludes the statement of `RothschildStein.rs3_no_drift_holder`
from `LiftApproximationNoDriftStatement` (the lifting theorem conclusion), the two P1 hypotheses
`DifferentiationTransferAllChartsNoDrift` (the type-calculus Props `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of the standard
frames of the no-drift charts; `TypeKernelIntegrable` is proved) and `ParametrixErrorTypesAllChartsNoDrift` (`ParametrixErrorTypes`
without drift), and the single doubling interface `LocalDoublingAllChartsNoDrift` (the local doubling property). Nothing else is assumed: the
upstream bundle `NoDriftHolderHypotheses` of `rs3_no_drift_holder_of_hypotheses` is assembled from these
(`leftDifferentiationAllChartsNoDrift_of_differentiationTransfer`, `higherHolderRegularityNoDrift_of_reducedHypotheses`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- **Higher Hölder regularity without drift from the P1 hypotheses** (BB pp. 603-604,
Thms 11.59-11.60, (11.94)-(11.96)): `HigherHolderRegularityNoDrift`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`), the P1 hypotheses (`DifferentiationTransferAllChartsNoDrift`, `ParametrixErrorTypesAllChartsNoDrift`) and the
doubling interface (`LocalDoublingAllChartsNoDrift`, the local doubling property), by `higherHolderRegularityNoDrift_of_hypotheses` with the derived
statements `holderTypeCalculusAllChartsNoDrift_of_differentiationTransfer`, `holderSignedParametrixAllChartsNoDrift_of_errorTypes` and
`liftedBaseHolderAllChartsNoDrift_of_reducedHypotheses`. -/
theorem higherHolderRegularityNoDrift_of_reducedHypotheses (liftApproximation : LiftApproximationNoDriftStatement) (hP : DifferentiationTransferAllChartsNoDrift)
    (hE : ParametrixErrorTypesAllChartsNoDrift) (hD : LocalDoublingAllChartsNoDrift) : HigherHolderRegularityNoDrift :=
  higherHolderRegularityNoDrift_of_hypotheses liftApproximation (holderTypeCalculusAllChartsNoDrift_of_differentiationTransfer hP)
    (holderSignedParametrixAllChartsNoDrift_of_errorTypes hE) (liftedBaseHolderAllChartsNoDrift_of_reducedHypotheses hP hE) hD

/-- BB Thm 11.1 (no drift, all `k`, Hölder): the statement of
`RothschildStein.rs3_no_drift_holder`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsNoDrift`), the parametrix error types
(`ParametrixErrorTypesAllChartsNoDrift`) and the doubling interface (`LocalDoublingAllChartsNoDrift`, the local doubling property); the row
integrability is proved (`LiftedChart.IsStandardFrame.typeKernelIntegrable`). -/
theorem rs3_no_drift_holder_of_reducedHypotheses (liftApproximation : LiftApproximationNoDriftStatement) (hP : DifferentiationTransferAllChartsNoDrift)
    (hE : ParametrixErrorTypesAllChartsNoDrift) (hD : LocalDoublingAllChartsNoDrift)
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
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX noDriftWeight X d Ω k α f →
        hasDistributionEquation Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc noDriftWeight X d Ω (k + 2) α u ∧
          holderXENorm noDriftWeight X d V (k + 2) α u ≤
            ENNReal.ofReal C *
              (holderXENorm noDriftWeight X d W k α f +
                eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin q → (Fin n → ℝ) → ℝ,
            (∀ i, hasIntrinsicWordDeriv X Ω [i, i] u (g i)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)), (∑ i, g i x) = f x) :=
  rs3_no_drift_holder_of_hypotheses
    ⟨liftApproximation, leftDifferentiationAllChartsNoDrift_of_differentiationTransfer hP, hD, higherHolderRegularityNoDrift_of_reducedHypotheses liftApproximation hP hE hD⟩ hn hq Ω V W
    hV hVW hW hWΩ X hX hspan k α hα hα1

end RothschildStein.P2
