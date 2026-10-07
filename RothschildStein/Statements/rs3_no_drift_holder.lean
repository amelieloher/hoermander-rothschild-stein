-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.hasDistributionEquation
public import RothschildStein.Definitions.controlDistance
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.memHolderXLoc
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.Definitions.hasIntrinsicWordDeriv
public import RothschildStein.Provider.rs3_no_drift_holder

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

theorem rs3_no_drift_holder
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
  by exact RothschildStein.Provider.rs3_no_drift_holder hn hq Ω V W hV hVW hW hWΩ X hX hspan k α hα hα1

end RothschildStein
