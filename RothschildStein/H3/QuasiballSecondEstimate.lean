-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RealSecondNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The proved real second-order quasiball estimate with its three
explicit constants, including the selected actual operator representative. -/
def SecondQuasiballEstimate {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (C a b : ℝ) : Prop :=
  ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
    ∀ u : (Fin n → ℝ) → ℝ,
      memSobolevX driftWeight X (quasiballDomain G ν x₀ s) 2 p u →
    ∀ D : WeakDriftOperatorData X (quasiballDomain G ν x₀ s) p u,
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ t) p u).toReal ≤
        C * ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
          b/(s-t)^2 * (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s))).toReal +
          2*a/(s-t) * (horizontalWeakENorm X (quasiballDomain G ν x₀ s) p u).toReal)

/-- The smooth quasiball cutoff gives geometry constants uniform in the
exponent. The analytic inputs are the compact second-order estimate and
global Sobolev density. -/
theorem second_quasiball_constants {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (p : ℝ≥0∞) (_hp : 1 ≤ p) (C : ℝ) (_hC : 0 ≤ C)
      (_hcompact : ∀ v : (Fin n → ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative H.fields I v) p volume ≤
            ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift H.fields v) p volume)
      (_hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
        Nonempty (SobolevWordApproximation driftWeight H.fields p v)),
      SecondQuasiballEstimate G ν H.fields p ((driftSecondWordFamily q).card * C) a b := by
  obtain ⟨c₁,c₂,hc₁,hc₂,hstep⟩ := quasiball_real_second_norm_of_compact_and_density G H ν hν
  refine ⟨c₁,(q+1 : ℝ)*c₂,hc₁,by positivity,?_⟩
  intro p hp C hC hcompact hdensity x₀ t s ht hts hhalf u hu D
  simpa only [mul_div_assoc] using
    hstep p hp C hC hcompact hdensity x₀ t s ht hts hhalf u hu D

end RothschildStein.H3
