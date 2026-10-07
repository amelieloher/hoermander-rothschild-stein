-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalSobolevRepresentativeCompactPv
public import RothschildStein.H3.FundamentalSecondCompactLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Every arbitrary distributional solution with local Lp forcing
has one representative in the exact fixed local Sobolev class. Geometry,
particular solutions, distribution patching, exhaustion, and gluing discharge
all analytic PV assumptions. -/
theorem local_sobolev_representative_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (p₀ : ℝ) (hp : 1 < p₀) (r : ℝ≥0∞)
    [Fact (1 ≤ ENNReal.ofReal p₀)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate (ENNReal.ofReal p₀) r]
    (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (g : (Fin N → ℝ) → ℝ)
    (hg : ∀ V : Opens (Fin N → ℝ), IsCompact (closure (V : Set (Fin N → ℝ))) →
      closure (V : Set (Fin N → ℝ)) ⊆ Ω →
      MemLp g (ENNReal.ofReal p₀) (volume.restrict (V : Set (Fin N → ℝ))))
    (heq : hasDistributionEquationWithDrift Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T g) :
    ∃ u : (Fin N → ℝ) → ℝ,
      memSobolevXLoc driftWeight H.fields Ω 2 (ENNReal.ofReal p₀) u ∧ representsDistribution Ω T u := by
  obtain ⟨M, hM, hPV⟩ := exists_fundamental_second_compact_Lp_bounds_of_controlNorm G H K C hp
  exact local_sobolev_representative_of_compact_principalValue_bounds G
    (standingWithNorm G H C.norm) (fundamentalKernelWithNorm G H C.norm K) hQ
    C.norm C.constant_one C.symmetric (ENNReal.ofReal p₀) r ENNReal.ofReal_ne_top M hM.le hPV Ω T g hg heq

end RothschildStein.H3
