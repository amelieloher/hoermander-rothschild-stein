-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDriftSobolev
public import RothschildStein.P1.StandardFrameIntegrability

/-!
# Local regularity with drift, `L^p`, `k = 0`: kernel integrability on standard frames

`TypeCalculusAllChartsDrift` (`LocalRegularityReducedDrift`) bundles the type-calculus Props `TypeKernelIntegrable`,
`LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of every standard frame of every drift chart. The first of them,
the row and column integrability of positive-type kernels (BB p. 544, Prop 11.10), is a theorem on every standard
frame (`LiftedChart.IsStandardFrame.typeKernelIntegrable`, from `LiftedChart.positiveType_rowIntegrable`).
`DifferentiationTransferAllChartsDrift` is the bundle without that conjunct, and `rs3_drift_sobolev_of_reducedHypotheses'` is
the root reduction of `rs3_drift_sobolev_of_reducedHypotheses` with the hypothesis `DifferentiationTransferAllChartsDrift`
(differentiation and transfer) and `ParametrixErrorTypesAllChartsDrift` (the parametrix error types) only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- The P1 type-calculus statements `TypeCalculusAllChartsDrift` without the row-integrability conjunct
`TypeKernelIntegrable`, which is proved on every standard frame (`LiftedChart.IsStandardFrame.typeKernelIntegrable`):
for every standard frame `F` of every lifted drift chart over a system with `3 ≤ n` and `0 < q`,
with every H1 fundamental kernel `K` of the drift model of the chart at the smooth homogeneous norm
of the chart group, left and right differentiation of type-`λ` operators (`LeftDifferentiation`, `RightDifferentiation`,
BB pp. 546-551, Thm 11.15) and transfer to the integration variable along the model bracket basis
`C.B` (`DerivativeTransfer`, BB pp. 552-559, Thm 11.24). -/
def DifferentiationTransferAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.driftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (hF : C.IsStandardFrame F (C.driftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn)),
    LeftDifferentiation F driftWeight C.Xl ∧
      RightDifferentiation F driftWeight C.Xl hF.lifted.contDiffOn_Xl ∧ DerivativeTransfer F driftWeight C.Xl C.B

/-- `TypeCalculusAllChartsDrift` follows from `DifferentiationTransferAllChartsDrift`: the row-integrability conjunct
is `LiftedChart.IsStandardFrame.typeKernelIntegrable`. -/
theorem typeCalculusAllChartsDrift_of_differentiationTransfer (h : DifferentiationTransferAllChartsDrift) : TypeCalculusAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact ⟨hF.typeKernelIntegrable, h hn hq C K F hF⟩

/-- BB Thm 11.2 (drift, `k = 0`, `L^p`): the statement of
`RothschildStein.rs3_drift_sobolev`, assuming the lifting theorem statement
(`LiftApproximationDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsDrift`) and the parametrix error types
(`ParametrixErrorTypesAllChartsDrift`); the row integrability is proved
(`LiftedChart.IsStandardFrame.typeKernelIntegrable`). -/
theorem rs3_drift_sobolev_of_reducedHypotheses' (liftApproximation : LiftApproximationDriftStatement) (hP : DifferentiationTransferAllChartsDrift)
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
  rs3_drift_sobolev_of_reducedHypotheses liftApproximation (typeCalculusAllChartsDrift_of_differentiationTransfer hP) hE hn hq Ω V W hV hVW hW hWΩ X
    hX hspan p hp hp_top

end RothschildStein.P2
