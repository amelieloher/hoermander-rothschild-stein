-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoFundamentalCompactPv
public import RothschildStein.H3.SmoothNormEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- The fundamental kernel's principal-value Lp bounds, horizontal flows,
and Sobolev approximation imply the scale-invariant estimate using the
compact second-order bound. -/
theorem smoothNorm_estimate_of_fundamental_compact_lp_flow_and_density {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    (hdensity : ∀ v, memSobolevX driftWeight H.fields ⊤ 2 p v →
      Nonempty (SobolevWordApproximation driftWeight H.fields p v)) :
    ∃ A : ℝ, 0 < A ∧ HalfRadiusEstimate G (G2.smoothNorm G) H.fields p A := by
  obtain ⟨C,hC,hcompact⟩ := compact_weight_two_estimate_of_fundamental_compact_principalValue_bounds G H K hQ p hp M hM hLp
  exact smoothNorm_estimate_of_compact_flow_and_density G H p hp hpt C hC.le hcompact
    E hE hE0 hflow hdensity

end RothschildStein.H3
