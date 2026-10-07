-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballStep
public import RothschildStein.H3.DriftSecondNormComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Step 1: the complete weighted second norm quasiball
estimate, including all mixed words and the drift, with uniform cutoff
constants and explicit finite-family coefficient. -/
theorem quasiball_second_norm_of_compact_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (p : ℝ≥0∞) (_hp : 1 ≤ p) (C : ℝ)
      (_hcompact : ∀ v : (Fin n → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative H.fields I v) p volume ≤
            ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift H.fields v) p volume)
      (_hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
        Nonempty (SobolevWordApproximation driftWeight H.fields p v)),
      ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν x₀ s) 2 p u →
      ∀ D : WeakDriftOperatorData H.fields (quasiballDomain G ν x₀ s) p u,
      driftSecondWeakENorm H.fields (quasiballDomain G ν x₀ t) p u ≤
          (driftSecondWordFamily q).card * ENNReal.ofReal C *
            (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
              (q+1 : ℝ≥0∞) * ENNReal.ofReal (c₂/(s-t)^2) *
                eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
              2 * ENNReal.ofReal (c₁/(s-t)) *
                ∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ s) [i.succ] p u) := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hstep⟩ := quasiball_step_of_compact_and_density G H ν hν
  refine ⟨c₁,c₂,hc₁,hc₂,?_⟩
  intro p hp C hcompact hdensity x₀ t s ht hts hhalf u hu D
  have hb := driftSecondWeakENorm_le_of_word_bounds H.fields (quasiballDomain G ν x₀ t)
    p u _ (hstep p hp C hcompact hdensity x₀ t s ht hts hhalf u hu D)
  simpa only [mul_assoc] using hb

end RothschildStein.H3
