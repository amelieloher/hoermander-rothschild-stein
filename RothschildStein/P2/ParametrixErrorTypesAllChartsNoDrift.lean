-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedNoDriftSobolev
public import RothschildStein.P2.LocalRegularityReducedNoDriftHolder
public import RothschildStein.P1.ErrorTypesLeftNoDrift

/-!
# Local regularity without drift: the parametrix error types are proved; the reduced roots

`ParametrixErrorTypesAllChartsNoDrift` (`LocalRegularityReducedNoDrift`) is the error-type step of the signed parametrix
(`ParametrixErrorTypesNoDrift`, BB pp. 561-563) for every standard frame of every lifted no-drift chart and all
cutoffs `a, b` of its region. `parametrixErrorTypesAllChartsNoDrift` proves it, from
`LiftedChart.parametrixErrorTypesNoDrift_of_isStandardFrame`.

`rs3_no_drift_sobolev_of_lift_and_differentiation` and `rs3_no_drift_holder_of_lift_and_differentiation` are the root reductions
`rs3_no_drift_sobolev_of_reducedHypotheses` and `rs3_no_drift_holder_of_reducedHypotheses` with that hypothesis discharged: they
conclude the statements of `RothschildStein.rs3_no_drift_sobolev` and
`RothschildStein.rs3_no_drift_holder` from `LiftApproximationNoDriftStatement` (the lifting theorem conclusion) and the
type-calculus hypotheses `DifferentiationTransferAllChartsNoDrift` only (Hölder: also the doubling interface
`LocalDoublingAllChartsNoDrift`, local doubling).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal
open RothschildStein.P1
namespace RothschildStein.P2

/-- The hypothesis `ParametrixErrorTypesAllChartsNoDrift` is in fact a theorem: for every standard frame of
every lifted no-drift chart (`3 ≤ n`, `0 < q`) and every H1 fundamental kernel `Γ` of the no-drift model at
the smooth homogeneous norm, the negated left error kernel is of type `1` modeled on `Γ*` and its transpose of
type `1` modeled on `Γ` (`LiftedChart.parametrixErrorTypesNoDrift_of_isStandardFrame`). -/
theorem parametrixErrorTypesAllChartsNoDrift : ParametrixErrorTypesAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C Γ F hF a b
  exact C.parametrixErrorTypesNoDrift_of_isStandardFrame hq (G2.smoothNorm C.G) Γ
    (C.two_lt_homogeneousDimension hn) hF a b

/-- BB Thm 11.1 (no drift, all `k`, `L^p`): the statement of
`RothschildStein.rs3_no_drift_sobolev`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`) and the type-calculus hypotheses (`DifferentiationTransferAllChartsNoDrift`); the row integrability and
the parametrix error types (`parametrixErrorTypesAllChartsNoDrift`) are proved. -/
theorem rs3_no_drift_sobolev_of_lift_and_differentiation (liftApproximation : LiftApproximationNoDriftStatement)
    (hP : DifferentiationTransferAllChartsNoDrift)
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
  rs3_no_drift_sobolev_of_reducedHypotheses liftApproximation hP parametrixErrorTypesAllChartsNoDrift hn hq Ω V W hV hVW hW hWΩ X hX hspan k
    p hp hp_top

/-- BB Thm 11.1 (no drift, all `k`, Hölder): the statement of
`RothschildStein.rs3_no_drift_holder`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`), the type-calculus hypotheses (`DifferentiationTransferAllChartsNoDrift`) and the doubling interface
(`LocalDoublingAllChartsNoDrift`, the local doubling property); the row integrability and the parametrix error types
(`parametrixErrorTypesAllChartsNoDrift`) are proved. -/
theorem rs3_no_drift_holder_of_lift_and_differentiation (liftApproximation : LiftApproximationNoDriftStatement) (hP : DifferentiationTransferAllChartsNoDrift)
    (hD : LocalDoublingAllChartsNoDrift)
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
  rs3_no_drift_holder_of_reducedHypotheses liftApproximation hP parametrixErrorTypesAllChartsNoDrift hD hn hq Ω V W hV hVW hW hWΩ X hX
    hspan k α hα hα1

end RothschildStein.P2
