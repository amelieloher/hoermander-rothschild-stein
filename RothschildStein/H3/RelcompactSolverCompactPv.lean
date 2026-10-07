-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.BoundedDomainSolverCompactPv
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The actual bounded-domain solver applies to every
open set with compact closure, with its constant fixed before the forcing. -/
theorem relcompact_solver_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (p r : ℝ≥0∞) [hpFact : Fact (1 ≤ p)] [hrFact : Fact (1 ≤ r)]
    [hpr : ENNReal.HolderConjugate p r] (hpt : p ≠ ∞)
    (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) p volume ≤
          ENNReal.ofReal M * eLpNorm F p volume)
    (V : Opens (Fin n → ℝ)) (hV : IsCompact (closure (V : Set (Fin n → ℝ)))) :
    ∃ A : ℝ, 0 < A ∧ ∀ g : (Fin n → ℝ) → ℝ,
      MemLp g p (volume.restrict (V : Set (Fin n → ℝ))) →
      ∃ v : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields V 2 p v ∧
        ∃ D : WeakDriftOperatorData H.fields V p v,
          D.operator =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] g ∧
          sobolevXENorm driftWeight H.fields V 2 p v ≤
            ENNReal.ofReal A * eLpNorm g p (volume.restrict (V : Set (Fin n → ℝ))) := by
  obtain ⟨B, hB⟩ := hV.bddAbove_image ν.gauge.1.continuousOn
  let ρ : ℝ := max 1 (B + 1)
  have hρ : 0 < ρ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsub : (V : Set (Fin n → ℝ)) ⊆ quasiballDomain G ν 0 ρ := by
    intro x hx
    rw [quasiballDomain_origin_set]
    have hxB : ν x ≤ B := hB ⟨x, subset_closure hx, rfl⟩
    exact lt_of_lt_of_le (by linarith : ν x < B + 1) (le_max_right _ _)
  obtain ⟨A, hA, hsolve⟩ := bounded_domain_solver_of_compact_principalValue_bounds
    G H K hQ ν h1 hsym ρ hρ p r hpt M hM hLp
  exact ⟨A, hA, fun g hg => hsolve V hsub g hg⟩

end RothschildStein.H3
