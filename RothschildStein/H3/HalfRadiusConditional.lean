-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusStep
public import RothschildStein.H3.InterpolationFullSecond

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- The full weighted half-radius estimate with a constant uniform in
center, radius, input function and certified operator representative. -/
def HalfRadiusEstimate {n q : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (K : ℝ) : Prop :=
  ∀ x₀ : Fin n → ℝ, ∀ r : ℝ, 0 < r → ∀ u : (Fin n → ℝ) → ℝ,
    memSobolevX driftWeight X (quasiballDomain G ν x₀ r) 2 p u →
    ∀ D : WeakDriftOperatorData X (quasiballDomain G ν x₀ r) p u,
      (driftSecondWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹*(horizontalWeakENorm X (quasiballDomain G ν x₀ (r/2)) p u).toReal +
      r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (r/2)))).toReal ≤
      K*((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal+
        r⁻¹^2*(eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ r))).toReal)

/-- The compact second-order estimate, horizontal flows, and global
Sobolev approximation imply the weighted scale-invariant local estimate. -/
theorem halfRadius_estimate_of_compact_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (C : ℝ) (hC : 0 ≤ C)
    (hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I v) p volume ≤
          ENNReal.ofReal C * eLpNorm (sumSquaresWithDrift H.fields v) p volume)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v)) :
    ∃ K : ℝ, 0 < K ∧ HalfRadiusEstimate G ν H.fields p K := by
  obtain ⟨a,b,ha,hb,hsecond⟩ := second_quasiball_constants G H ν hν
  obtain ⟨cE,δE,hcE,hδE,hfirst⟩ := interpolation_full_second_of_flow_and_density G H ν hν
  let Cstar : ℝ := (driftSecondWordFamily q).card*C
  have hCstar : 0 ≤ Cstar := mul_nonneg (Nat.cast_nonneg _) hC
  obtain ⟨δ,hδ,hdE,hsmall⟩ := exists_localEstimate_absorption_parameter
    (show 0 ≤ 8*a*Cstar by positivity) hδE
  let B := 2*(4*b*Cstar+(8*a*Cstar)*cE/δ)
  let K := 1+(4+2*δ)*(Cstar/2)+(4+2*δ)*B+2*cE/δ
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro x₀ r hr u hu D
  exact (halfRadius_estimate_with_constants G ν H.fields p hCstar ha.le hb.le hcE.le
    hδ hsmall (hsecond p hp C hC hcompact hdensity) x₀ hr u hu D
    (hfirst E hE hE0 hflow p hp hpt hdensity x₀ r hr u hu δ hδ hdE)).2

end RothschildStein.H3
