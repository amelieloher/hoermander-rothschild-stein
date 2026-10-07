-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSolverCompactPv
public import RothschildStein.H3.CompactSourceApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter Set
open scoped ENNReal Topology

/-- The fundamental solver constructs its smooth source approximation internally. -/
theorem compact_source_solver_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (σ : ℝ) (hσ : 0 < σ)
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (hpt : p ≠ ∞)
    (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) p volume ≤
          ENNReal.ofReal M*eLpNorm F p volume) :
    ∃ (C : ℝ → List (Fin (q+1)) → ℝ) (C₉ : ℝ), 0 < C₉ ∧
      (∀ R : ℝ, 0 < R → ∀ I ∈ wordFamily driftWeight 2, 0 < C R I) ∧
      ∀ (F : (Fin n → ℝ) → ℝ), MemLp F p volume →
        (∀ᵐ y ∂volume, σ ≤ ν y → F y = 0) →
        ConvolutionLocalSolutions G H ν p F K C ∧
        memSobolevXLoc driftWeight H.fields ⊤ 2 p (G2.groupConvolution G F K) ∧
        driftSecondWeakENorm H.fields ⊤ p (G2.groupConvolution G F K) ≤
          (driftSecondWordFamily q).card*ENNReal.ofReal C₉*eLpNorm F p volume := by
  obtain ⟨C, C₉, hC₉, hC, hsolve⟩ := fundamental_solver_of_compact_principalValue_bounds
    G H K hQ ν h1 hsym (σ + 1) (by linarith) p r M hM hLp
  refine ⟨C, C₉, hC₉, hC, ?_⟩
  intro F hF hsF
  have hpR : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal (by norm_num) hpt).mpr (Fact.out : 1 ≤ p)
  have hFR : MemLp F (ENNReal.ofReal p.toReal) volume := by
    simpa only [ENNReal.ofReal_toReal hpt] using hF
  obtain ⟨f, hfs, hft⟩ := exists_smooth_source_approximation G ν h1 hpR hFR hsF
  have hft' : Tendsto (fun j => eLpNorm (f j - F) p volume) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_toReal hpt] using hft
  apply hsolve f F hF (fun j => (hfs j).1) (fun j => (hfs j).2.1) _ _ hft'
  · filter_upwards [hsF] with y hy
    intro h
    exact hy (by linarith)
  · intro j
    exact Eventually.of_forall (hfs j).2.2

end RothschildStein.H3
