-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDriftDifferentiation
public import RothschildStein.P2.LocalRegularityReducedDriftHolder
public import RothschildStein.P1.ErrorTypesLeft

/-!
# Local regularity with drift: the parametrix error types are proved; the reduced roots

`ParametrixErrorTypesAllChartsDrift` (`LocalRegularityReducedDrift`) is the error-type step of the signed parametrix (`ParametrixErrorTypes`, BB
pp. 561-563) for every standard frame of every lifted drift chart and all cutoffs `a, b` of its region.
`parametrixErrorTypesAllChartsDrift` proves it: it is `LiftedChart.parametrixErrorTypes_of_isStandardFrame` (the error kernel of the
left parametrix and its transpose are of type `1` modeled on `Γ*` resp. `Γ`).

`rs3_drift_sobolev_of_lift_and_differentiation` and `rs3_drift_holder_of_lift_and_differentiation` are the root reductions
`rs3_drift_sobolev_of_reducedHypotheses'` and `rs3_drift_holder_of_reducedHypotheses` with that hypothesis discharged: they
conclude the statements of `RothschildStein.rs3_drift_sobolev` and `RothschildStein.rs3_drift_holder`
from `LiftApproximationDriftStatement` (the lifting theorem conclusion) and the type-calculus hypotheses `DifferentiationTransferAllChartsDrift` only
(Hölder: also the doubling interface `LocalDoublingAllChartsDrift`, the local doubling property).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- The hypothesis `ParametrixErrorTypesAllChartsDrift` is in fact a theorem: for every standard frame of
every lifted drift chart (`3 ≤ n`, `0 < q`) and every H1 fundamental kernel `Γ` of the drift model at the
smooth homogeneous norm, the negated left error kernel is of type `1` modeled on `Γ*` and its transpose of
type `1` modeled on `Γ` (`LiftedChart.parametrixErrorTypes_of_isStandardFrame`). -/
theorem parametrixErrorTypesAllChartsDrift : ParametrixErrorTypesAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C Γ F hF a b
  exact C.parametrixErrorTypes_of_isStandardFrame hq (G2.smoothNorm C.G) Γ
    (C.two_lt_homogeneousDimension hn) hF a b

/-- BB Thm 11.2 (drift, `k = 0`, `L^p`): the statement of
`RothschildStein.rs3_drift_sobolev`, assuming the lifting theorem statement
(`LiftApproximationDriftStatement`) and the type-calculus hypotheses (`DifferentiationTransferAllChartsDrift`); the row integrability
(`LiftedChart.IsStandardFrame.typeKernelIntegrable`) and the parametrix error types (`parametrixErrorTypesAllChartsDrift`) are
proved. -/
theorem rs3_drift_sobolev_of_lift_and_differentiation (liftApproximation : LiftApproximationDriftStatement) (hP : DifferentiationTransferAllChartsDrift)
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
  rs3_drift_sobolev_of_reducedHypotheses' liftApproximation hP parametrixErrorTypesAllChartsDrift hn hq Ω V W hV hVW hW hWΩ X hX hspan p hp
    hp_top

/-- BB Thm 11.2 (drift, `k = 0`, Hölder): the statement of
`RothschildStein.rs3_drift_holder`, assuming the lifting theorem statement
(`LiftApproximationDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsDrift`) and the doubling interface
(`LocalDoublingAllChartsDrift`, the local doubling property); the row integrability and the parametrix error types (`parametrixErrorTypesAllChartsDrift`) are
proved. -/
theorem rs3_drift_holder_of_lift_and_differentiation (liftApproximation : LiftApproximationDriftStatement) (hP : DifferentiationTransferAllChartsDrift)
    (hD : LocalDoublingAllChartsDrift)
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
  rs3_drift_holder_of_reducedHypotheses liftApproximation hP parametrixErrorTypesAllChartsDrift hD hn hq Ω V W hV hVW hW hWΩ X hX hspan α hα
    hα1

end RothschildStein.P2
