-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalGlobalConditional
public import RothschildStein.H3.SobolevDomainRestrictionNorm
public import RothschildStein.H3.WeakDriftOperatorRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Restrict the fundamental convolution and its operator jets to a
bounded domain, preserving the forcing and fixed Sobolev bound. -/
theorem convolution_solution_restrict {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (p : ℝ≥0∞)
    (F K : (Fin n → ℝ) → ℝ) (C : ℝ → List (Fin (q + 1)) → ℝ)
    (hsol : ConvolutionLocalSolutions G H ν p F K C)
    {ρ : ℝ} (hρ : 0 < ρ) (Ω : Opens (Fin n → ℝ))
    (hΩ : (Ω : Set (Fin n → ℝ)) ⊆ quasiballDomain G ν 0 ρ)
    (hC : ∀ I ∈ wordFamily driftWeight 2, 0 ≤ C ρ I) :
    memSobolevX driftWeight H.fields Ω 2 p (G2.groupConvolution G F K) ∧
      ∃ D : WeakDriftOperatorData H.fields Ω p (G2.groupConvolution G F K),
        D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F ∧
        sobolevXENorm driftWeight H.fields Ω 2 p (G2.groupConvolution G F K) ≤
          ENNReal.ofReal (∑ I ∈ wordFamily driftWeight 2, C ρ I) * eLpNorm F p volume := by
  obtain ⟨hu, D, hop, hb⟩ := hsol ρ hρ
  refine ⟨S.memSobolevX_restrict driftWeight H.fields _ Ω hΩ hu, D.restrict Ω hΩ, ?_, ?_⟩
  · rw [D.restrict_operator]
    exact hop.filter_mono (ae_mono (Measure.restrict_mono_set volume hΩ))
  · have hs := Finset.sum_le_sum (s := wordFamily driftWeight 2) hb
    have hn : sobolevXENorm driftWeight H.fields (quasiballDomain G ν 0 ρ) 2 p
        (G2.groupConvolution G F K) ≤
        ENNReal.ofReal (∑ I ∈ wordFamily driftWeight 2, C ρ I) * eLpNorm F p volume := by
      simpa only [sobolevXENorm, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hC] using hs
    exact (sobolevXENorm_mono_domain driftWeight H.fields _ Ω hΩ 2 p _ hu).trans hn

end RothschildStein.H3
