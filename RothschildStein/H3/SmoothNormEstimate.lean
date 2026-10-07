-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusConditional
public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal

/-- for the canonical smooth gauge, with a constant fixed
before the center, radius, input and operator representative. -/
theorem smoothNorm_estimate_of_compact_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
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
    ∃ K : ℝ, 0 < K ∧ HalfRadiusEstimate G (G2.smoothNorm G) H.fields p K :=
  halfRadius_estimate_of_compact_flow_and_density G H (G2.smoothNorm G)
    (G2.smoothNorm_smooth G) p hp hpt C hC hcompact E hE hE0 hflow hdensity

end RothschildStein.H3
