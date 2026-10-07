-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondCompactLp
public import RothschildStein.H3.BoundedDomainSolverCompactPv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Every Lp forcing on a bounded open domain has an actual
fundamental potential solution with the full fixed Sobolev estimate.
Only exact control geometry is an upstream certificate; all PV bounds and
source approximation are constructed internally. -/
theorem bounded_domain_solver_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (ρ : ℝ) (hρ : 0 < ρ) (p₀ : ℝ) (hp : 1 < p₀) (r : ℝ≥0∞)
    [Fact (1 ≤ ENNReal.ofReal p₀)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate (ENNReal.ofReal p₀) r] :
    ∃ A : ℝ, 0 < A ∧ ∀ Ω : Opens (Fin N → ℝ),
      (Ω : Set (Fin N → ℝ)) ⊆ quasiballDomain G ν 0 ρ →
      ∀ f : (Fin N → ℝ) → ℝ, MemLp f (ENNReal.ofReal p₀) (volume.restrict (Ω : Set (Fin N → ℝ))) →
      ∃ u : (Fin N → ℝ) → ℝ, memSobolevX driftWeight H.fields Ω 2 (ENNReal.ofReal p₀) u ∧
        ∃ D : WeakDriftOperatorData H.fields Ω (ENNReal.ofReal p₀) u,
          D.operator =ᵐ[volume.restrict (Ω : Set (Fin N → ℝ))] f ∧
          sobolevXENorm driftWeight H.fields Ω 2 (ENNReal.ofReal p₀) u ≤
            ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p₀) (volume.restrict (Ω : Set (Fin N → ℝ))) := by
  obtain ⟨M, hM, hPV⟩ := exists_fundamental_second_compact_Lp_bounds_of_controlNorm G H K C hp
  exact bounded_domain_solver_of_compact_principalValue_bounds G (standingWithNorm G H C.norm)
    (fundamentalKernelWithNorm G H C.norm K) hQ ν h1 hsym ρ hρ
    (ENNReal.ofReal p₀) r ENNReal.ofReal_ne_top M hM.le hPV

end RothschildStein.H3
