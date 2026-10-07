-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondOrderDensity
public import RothschildStein.H3.WeakDriftOperatorUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- The second-word estimate holds for any selected certified
operator representative, by weak operator uniqueness. -/
theorem second_orders_for_operator_of_compact_and_density {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (C : ℝ)
    (hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative X I v) p volume ≤
          ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift X v) p volume)
    (hdensity : ∀ u, memSobolevX driftWeight X ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight X p u))
    (u : (Fin n → ℝ) → ℝ) (hu : memSobolevX driftWeight X ⊤ 2 p u)
    (E : WeakDriftOperatorData X ⊤ p u) :
    ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
      weakWordENorm X ⊤ I p u ≤ ENNReal.ofReal C * eLpNorm E.operator p volume := by
  obtain ⟨D, _, _, hb⟩ := second_orders_of_compact_and_density X hX p hp C
    hcompact hdensity u hu
  have he := D.operator_ae_eq E (fun i => (hX i).contDiffOn) hp
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at he
  intro I hI
  simpa only [eLpNorm_congr_ae he] using hb I hI

end RothschildStein.H3
