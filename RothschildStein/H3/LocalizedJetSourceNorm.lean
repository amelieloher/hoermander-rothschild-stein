-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedJetSource
public import RothschildStein.H3.DriftCutoffGlobalNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The localized ordered jet source is the shared weak drift
cutoff expression, rather than a separately chosen operator value. -/
theorem localized_jet_source_eq_cutoff {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (p : ℝ≥0∞) (u φ : (Fin N → ℝ) → ℝ)
    (D : WeakDriftOperatorData X Ω p u)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u) (hfirst : ∀ i, jet [i] = D.first i)
    (hsquare : ∀ i : Fin q, jet [i.succ, i.succ] = D.square i) :
    (fun x => S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x) =
      driftCutoffExpression D φ := by
  funext x
  rw [localized_jet_source X u φ jet hzero x]
  simp only [hfirst, hsquare, driftCutoffExpression, WeakDriftOperatorData.operator]
  simp only [mul_comm]
  ring

/-- The actual compact cutoff source has the established
local weak norm bound, including the endpoint p infinity. -/
theorem localized_jet_source_norm_le {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u : (Fin N → ℝ) → ℝ) (D : WeakDriftOperatorData X Ω p u)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u) (hfirst : ∀ i, jet [i] = D.first i)
    (hsquare : ∀ i : Fin q, jet [i.succ, i.succ] = D.square i)
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (A B : ℝ≥0∞)
    (hφ : eLpNorm φ ⊤ (volume.restrict (Ω : Set (Fin N → ℝ))) ≤ 1)
    (hA : ∀ i : Fin q, eLpNorm (fieldDerivative (X i.succ) φ) ⊤
      (volume.restrict (Ω : Set (Fin N → ℝ))) ≤ A)
    (hB : eLpNorm (sumSquaresWithDrift X φ) ⊤
      (volume.restrict (Ω : Set (Fin N → ℝ))) ≤ B) :
    eLpNorm (fun x => S.leibnizWordValue X [0] jet φ x +
      ∑ i : Fin q, S.leibnizWordValue X [i.succ, i.succ] jet φ x) p volume ≤
      eLpNorm D.operator p (volume.restrict (Ω : Set (Fin N → ℝ))) +
        B * eLpNorm u p (volume.restrict (Ω : Set (Fin N → ℝ))) +
        2 * A * ∑ i : Fin q, weakWordENorm X Ω [i.succ] p u := by
  rw [localized_jet_source_eq_cutoff X Ω p u φ D jet hzero hfirst hsquare]
  exact driftCutoffExpression_global_norm_le_of_bounds X Ω p hp u D φ A B hφ hA hB

end RothschildStein.H3
