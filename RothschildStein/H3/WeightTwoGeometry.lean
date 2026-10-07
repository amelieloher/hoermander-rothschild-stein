-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoFundamentalCompactPv
public import RothschildStein.H3.FundamentalSecondCompactLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RothschildStein.H3

/-- The actual compact smooth a priori estimate for every
weight-two word. All fundamental PV estimates and correction coefficients
are constructed from exact control geometry. -/
theorem compact_weight_two_estimate_of_fundamental_kernel_and_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields)
    {p : ℝ} (hp : 1 < p) :
    ∃ A : ℝ, 0 < A ∧ ∀ u : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I u) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal A * eLpNorm (sumSquaresWithDrift H.fields u) (ENNReal.ofReal p) volume := by
  obtain ⟨M, hM, hPV⟩ := exists_fundamental_second_compact_Lp_bounds_of_controlNorm G H K P hp
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  exact compact_weight_two_estimate_of_fundamental_compact_principalValue_bounds G
    (standingWithNorm G H P.norm) (fundamentalKernelWithNorm G H P.norm K)
    hQ (ENNReal.ofReal p) hp₁ M hM.le hPV

end RothschildStein.H3
