-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DistributionPatchCompactPv
public import RothschildStein.H3.RelcompactOpenExhaustion
public import RothschildStein.H3.SobolevExhaustionGluing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The arbitrary fixed distributional solution with local
Lp forcing has one actual representative in the literal fixed local
Sobolev class. Particular solutions, exhaustion, and gluing are constructed. -/
theorem local_sobolev_representative_of_compact_principalValue_bounds {n q : ℕ}
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
    (Ω : Opens (Fin n → ℝ)) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (g : (Fin n → ℝ) → ℝ)
    (hg : ∀ V : Opens (Fin n → ℝ), IsCompact (closure (V : Set (Fin n → ℝ))) →
      closure (V : Set (Fin n → ℝ)) ⊆ Ω →
      MemLp g p (volume.restrict (V : Set (Fin n → ℝ))))
    (heq : hasDistributionEquationWithDrift Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) T g) :
    ∃ u : (Fin n → ℝ) → ℝ,
      memSobolevXLoc driftWeight H.fields Ω 2 p u ∧ representsDistribution Ω T u := by
  classical
  obtain ⟨U, hmono, hUk, hcover, hcofinal⟩ := exists_relcompact_open_exhaustion Ω
  have hpatch (j : ℕ) : ∃ v : (Fin n → ℝ) → ℝ,
      memSobolevX driftWeight H.fields (U j) 2 p v ∧
      ∀ ψ : TestFunction (U j) ℝ (⊤ : ℕ∞),
        T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x * v x := by
    have houter : closure (U (j + 1) : Set (Fin n → ℝ)) ⊆ Ω :=
      (hUk (j + 1)).2.1.trans (hUk (j + 1 + 1)).2.2
    obtain ⟨v, hv, _, _, hrep⟩ := distribution_patch_of_compact_principalValue_bounds
      G H K hQ ν h1 hsym p r hpt M hM hLp Ω (U (j + 1)) (U j)
      (hUk (j + 1)).2.2 (hUk (j + 1)).1 (hUk j).1 (hUk j).2.1 T g
      (hg _ (hUk (j + 1)).1 houter) heq
    exact ⟨v, hv, hrep⟩
  choose v hv using hpatch
  exact exists_local_sobolev_representative_of_exhaustion Ω U hmono
    (fun j => (hUk j).2.2) hcover hcofinal driftWeight H.fields 2 p
    (Fact.out : 1 ≤ p) T v hv

end RothschildStein.H3
