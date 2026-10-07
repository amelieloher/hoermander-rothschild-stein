-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballSecondNorm
public import RothschildStein.H3.SecondStepToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The actual finite weak norms give the real second-order
quasiball step for Phi absorption, preserving all cutoff coefficients. -/
theorem quasiball_real_second_norm_of_compact_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (p : ℝ≥0∞) (_hp : 1 ≤ p) (C : ℝ) (_hC : 0 ≤ C)
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
      (driftSecondWeakENorm H.fields (quasiballDomain G ν x₀ t) p u).toReal ≤
        ((driftSecondWordFamily q).card : ℝ) * C *
          ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
            (q+1 : ℝ) * (c₂/(s-t)^2) *
              (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
            2 * (c₁/(s-t)) *
              (horizontalWeakENorm H.fields (quasiballDomain G ν x₀ s) p u).toReal) := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hstep⟩ := quasiball_second_norm_of_compact_and_density G H ν hν
  refine ⟨c₁,c₂,hc₁,hc₂,?_⟩
  intro p hp C hC hcompact hdensity x₀ t s ht hts hhalf u hu D
  have hb := hstep p hp C hcompact hdensity x₀ t s ht hts hhalf u hu D
  have hF : eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s)) ≠ ⊤ :=
    D.operator_memLp.eLpNorm_ne_top
  have hU := hu.1.eLpNorm_ne_top
  have hV : (∑ i : Fin q, weakWordENorm H.fields (quasiballDomain G ν x₀ s) [i.succ] p u) ≠ ⊤ :=
    ne_of_lt (horizontalWeakENorm_lt_top H.fields (quasiballDomain G ν x₀ s) p u hu)
  have hgap : 0 < s-t := sub_pos.mpr hts
  exact second_norm_step_toReal (driftSecondWordFamily q).card q hF hU hV hC
    (div_nonneg hc₁.le hgap.le) (div_nonneg hc₂.le (sq_nonneg _)) hb

end RothschildStein.H3
