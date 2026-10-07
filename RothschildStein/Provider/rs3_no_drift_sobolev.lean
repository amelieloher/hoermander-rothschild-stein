-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.exists_lift_approximation_noDrift
public import RothschildStein.P2.DifferentiationTransferStandard
public import RothschildStein.P2.LocalRegularityRootNoDriftSobolev
public import RothschildStein.P2.LocalRegularityReducedNoDriftSobolev
public import RothschildStein.P2.ParametrixErrorTypesAllChartsNoDrift

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein.Provider

/-- The Sobolev estimate for fields without drift follows from the lift approximation and the standard-frame estimates;
the required error types are included in the assembly. -/
theorem rs3_no_drift_sobolev_of_lift_and_differentiation (liftApproximation : P2.LiftApproximationNoDriftStatement) (hP : P2.DifferentiationTransferAllChartsNoDrift)
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
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  exact P2.rs3_no_drift_sobolev_of_lift_and_differentiation liftApproximation hP hn hq Ω V W hV hVW hW hWΩ X hX hspan k p hp hp_top

/-- The Sobolev estimate for fields without drift follows from `exists_lift_approximation_noDrift`,
the standard-frame estimates, error-type bounds, and local doubling estimate
from their proved providers. -/
theorem rs3_no_drift_sobolev
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
                eLpNorm u p (volume.restrict (W : Set (Fin n → ℝ)))) := by
  exact rs3_no_drift_sobolev_of_lift_and_differentiation (by intro n q; exact @exists_lift_approximation_noDrift n q)
    P2.differentiationTransferAllChartsNoDrift_holds hn hq Ω V W hV hVW hW hWΩ X hX hspan k p hp hp_top

end RothschildStein.Provider
