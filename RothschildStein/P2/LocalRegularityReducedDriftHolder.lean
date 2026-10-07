-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDriftHolderLifted
public import RothschildStein.P2.LocalRegularityRootDriftHolder

/-!
# Local regularity with drift, Hölder, `k = 0` (BB Thm 11.2): the root reduced to the P1 hypotheses

`rs3_drift_holder_of_reducedHypotheses` concludes the statement of `RothschildStein.rs3_drift_holder`
from `LiftApproximationDriftStatement` (the lifting theorem conclusion), the two P1 hypotheses
`DifferentiationTransferAllChartsDrift` (the type-calculus Props `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of the
standard frames of the drift charts; the row integrability is proved) and `ParametrixErrorTypesAllChartsDrift`
(the parametrix error types `ParametrixErrorTypes`), and the single doubling interface `LocalDoublingAllChartsDrift` (the local doubling property). Nothing else is
assumed: the upstream bundle `DriftHolderHypotheses` of `rs3_drift_holder_of_hypotheses` is assembled
from these (`leftDifferentiationAllChartsDrift_of_typeCalculus`, `typeCalculusAllChartsDrift_of_differentiationTransfer`, `liftedBaseHolderAllChartsDrift_of_reducedHypotheses`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- BB Thm 11.2 (drift, `k = 0`, Hölder): the statement of
`RothschildStein.rs3_drift_holder`, assuming the lifting theorem statement
(`LiftApproximationDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsDrift`), the parametrix error types
(`ParametrixErrorTypesAllChartsDrift`) and the doubling interface (`LocalDoublingAllChartsDrift`, the local doubling property); the row
integrability is proved (`LiftedChart.IsStandardFrame.typeKernelIntegrable`). -/
theorem rs3_drift_holder_of_reducedHypotheses (liftApproximation : LiftApproximationDriftStatement) (hP : DifferentiationTransferAllChartsDrift)
    (hE : ParametrixErrorTypesAllChartsDrift) (hD : LocalDoublingAllChartsDrift)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    let d := controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memHolderX driftWeight X d Ω 0 α f →
        hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          ContinuousOn u (Ω : Set (Fin n → ℝ)) ∧
          memHolderXLoc driftWeight X d Ω 2 α u ∧
          holderXENorm driftWeight X d V 2 α u ≤
            ENNReal.ofReal C *
              (holderXENorm driftWeight X d W 0 α f +
                eLpNorm u ⊤ (volume.restrict (W : Set (Fin n → ℝ)))) ∧
          ∃ g : Fin (q + 1) → (Fin n → ℝ) → ℝ,
            hasIntrinsicWordDeriv X Ω [0] u (g 0) ∧
            (∀ i : Fin q,
              hasIntrinsicWordDeriv X Ω [i.succ, i.succ] u (g i.succ)) ∧
            (∀ x ∈ (Ω : Set (Fin n → ℝ)),
              (∑ i : Fin q, g i.succ x) + g 0 x = f x) :=
  rs3_drift_holder_of_hypotheses
    ⟨liftApproximation, leftDifferentiationAllChartsDrift_of_typeCalculus (typeCalculusAllChartsDrift_of_differentiationTransfer hP), hD,
      liftedBaseHolderAllChartsDrift_of_reducedHypotheses hP hE⟩ hn hq Ω V W hV hVW hW hWΩ X hX hspan α hα hα1

end RothschildStein.P2
