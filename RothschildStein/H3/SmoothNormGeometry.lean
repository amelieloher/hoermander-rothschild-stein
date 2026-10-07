-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoGeometry
public import RothschildStein.H3.SmoothNormEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- The fundamental kernel's principal-value Lp bounds, horizontal flows,
and Sobolev approximation imply the scale-invariant estimate using the
compact second-order bound. -/
theorem smoothNorm_estimate_of_geometry_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hp₁ : 1 < p.toReal)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v)) :
    ∃ A : ℝ, 0 < A ∧ HalfRadiusEstimate G (G2.smoothNorm G) H.fields p A := by
  obtain ⟨A, hA, hb⟩ := compact_weight_two_estimate_of_fundamental_kernel_and_controlNorm G H K hQ P hp₁
  have hcompact : ∀ v : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I v) p volume ≤
          ENNReal.ofReal A * eLpNorm (sumSquaresWithDrift H.fields v) p volume := by
    simpa only [ENNReal.ofReal_toReal hpt] using hb
  exact smoothNorm_estimate_of_compact_flow_and_density G H p hp hpt A hA.le hcompact
    E hE hE0 hflow hdensity

end RothschildStein.H3
