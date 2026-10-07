-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDrift
public import RothschildStein.P2.LocalRegularityRootDriftSobolev

/-!
# Local regularity with drift, `L^p`, `k = 0` (BB Thm 11.2): the root reduced to the P1 hypotheses

`rs3_drift_sobolev_of_reducedHypotheses` concludes the statement of `RothschildStein.rs3_drift_sobolev`
from `LiftApproximationDriftStatement` (the lifting theorem conclusion) and the two P1 hypotheses
`TypeCalculusAllChartsDrift` (the type-calculus Props `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`
of the standard frames of the drift charts) and `ParametrixErrorTypesAllChartsDrift` (`ParametrixErrorTypes`). Nothing else
is assumed: the upstream bundle `DriftSobolevHypotheses` of `rs3_drift_sobolev_of_hypotheses` is
assembled from these (`leftDifferentiationAllChartsDrift_of_typeCalculus`, `liftedBaseSobolevAllChartsDrift_of_reducedHypotheses`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- BB Thm 11.2 (drift, `k = 0`, `L^p`): the statement of
`RothschildStein.rs3_drift_sobolev`, assuming the lifting theorem statement
(`LiftApproximationDriftStatement`) and the P1 hypotheses (`TypeCalculusAllChartsDrift`, `ParametrixErrorTypesAllChartsDrift`). -/
theorem rs3_drift_sobolev_of_reducedHypotheses (liftApproximation : LiftApproximationDriftStatement) (hP : TypeCalculusAllChartsDrift)
    (hE : ParametrixErrorTypesAllChartsDrift)
    {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (Ω V W : Opens (Fin n → ℝ))
    (hV : IsCompact (closure (V : Set (Fin n → ℝ))))
    (hVW : closure (V : Set (Fin n → ℝ)) ⊆ (W : Set (Fin n → ℝ)))
    (hW : IsCompact (closure (W : Set (Fin n → ℝ))))
    (hWΩ : closure (W : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X)
    (p : ℝ≥0∞) (hp : 1 < p) (hp_top : p < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin n → ℝ) → ℝ),
        memSobolevX driftWeight X Ω 0 p f →
        hasDistributionEquationWithDrift Ω X hX T f →
        ∃ u : (Fin n → ℝ) → ℝ,
          LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume ∧
          T = Distribution.ofFun Ω u volume (⊤ : ℕ∞) ∧
          memSobolevXLoc driftWeight X Ω 2 p u ∧
          sobolevXENorm driftWeight X V 2 p u ≤
            ENNReal.ofReal C *
              (sobolevXENorm driftWeight X W 0 p f +
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) :=
  rs3_drift_sobolev_of_hypotheses
    ⟨liftApproximation, leftDifferentiationAllChartsDrift_of_typeCalculus hP, liftedBaseSobolevAllChartsDrift_of_reducedHypotheses hP hE⟩ hn hq Ω V W hV hVW hW
    hWΩ X hX hspan p hp hp_top

end RothschildStein.P2
