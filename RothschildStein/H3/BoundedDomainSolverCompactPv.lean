-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionRestriction
public import RothschildStein.H3.CompactSourceSolverCompactPv
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The fundamental convolution solves each Lp forcing on a bounded open
subset of the fixed origin ball under the compact first-order principal-value
bounds. The type-II dimension hypothesis is Q > 2. -/
theorem bounded_domain_solver_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (ρ : ℝ) (hρ : 0 < ρ)
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (hpt : p ≠ ∞) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ F : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 F → HasCompactSupport F →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) p volume ≤
          ENNReal.ofReal M * eLpNorm F p volume) :
    ∃ A : ℝ, 0 < A ∧ ∀ Ω : Opens (Fin n → ℝ),
      (Ω : Set (Fin n → ℝ)) ⊆ quasiballDomain G ν 0 ρ →
      ∀ f : (Fin n → ℝ) → ℝ, MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ))) →
      ∃ u : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields Ω 2 p u ∧
        ∃ D : WeakDriftOperatorData H.fields Ω p u,
          D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] f ∧
          sobolevXENorm driftWeight H.fields Ω 2 p u ≤
            ENNReal.ofReal A * eLpNorm f p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  obtain ⟨C, C₉, _, hC, hsolve⟩ := compact_source_solver_of_compact_principalValue_bounds
    G H K hQ ν h1 hsym ρ hρ p r hpt M hM hLp
  let S : ℝ := ∑ I ∈ wordFamily driftWeight 2, C ρ I
  have hS : 0 ≤ S := Finset.sum_nonneg (fun I hI => (hC ρ hρ I hI).le)
  refine ⟨1 + S, by positivity, ?_⟩
  intro Ω hΩ f hf
  let F := (Ω : Set (Fin n → ℝ)).indicator f
  have hF : MemLp F p (volume : Measure (Fin n → ℝ)) :=
    (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).mpr hf
  have hsF : ∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0 := by
    apply Filter.Eventually.of_forall
    intro y hy
    have hn : y ∉ (Ω : Set (Fin n → ℝ)) := by
      intro hm
      have hh := hΩ hm
      rw [quasiballDomain_origin_set] at hh
      exact (not_lt_of_ge hy) hh
    exact indicator_of_notMem hn f
  have hsol := (hsolve F hF hsF).1
  obtain ⟨hu, D, hop, hb⟩ := convolution_solution_restrict G H ν p F K C hsol hρ Ω hΩ
    (fun I hI => (hC ρ hρ I hI).le)
  have hFf : F =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] f := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    exact indicator_of_mem hy f
  have hnorm : eLpNorm F p volume = eLpNorm f p (volume.restrict (Ω : Set (Fin n → ℝ))) :=
    eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet
  refine ⟨G2.groupConvolution G F K, hu, D, hop.trans hFf, ?_⟩
  rw [hnorm] at hb
  exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by change S ≤ 1 + S; linarith)) le_rfl)

end RothschildStein.H3
