-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.MollifierInteriorSupport
public import RothschildStein.H3.HolderMollifierCauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal
namespace RothschildStein.H3

/-- Group mollification gives smooth
compact approximants in the original open ball, uniform convergence,
exact Hölder norm contractions, and two-scale lower-exponent Cauchy
convergence (BB Theorem 8.52, pp. 381–382). -/
theorem group_mollification {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (φ : G2.GroupMollifier G ν) {ρ : ℝ} {a : ℝ≥0} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ν x < ρ}) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.BoundedHolder (ControlCarrier N) metric a univ f →
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      ContDiff ℝ (⊤ : ℕ∞) (G2.groupRegularize G φ f ε) ∧
      HasCompactSupport (G2.groupRegularize G φ f ε) ∧
      tsupport (G2.groupRegularize G φ f ε) ⊆ {x | ν x < ρ}) ∧
    TendstoUniformly (fun ε : ℝ => G2.groupRegularize G φ f ε) f (𝓝[>] 0) ∧
    (∀ ε : ℝ, 0 < ε →
      H2.holderSup univ (G2.groupRegularize G φ f ε) ≤ H2.holderSup univ f ∧
      @H2.holderSemi (ControlCarrier N) metric a univ (G2.groupRegularize G φ f ε) ≤
        @H2.holderSemi (ControlCarrier N) metric a univ f ∧
      @H2.boundedHolderNorm (ControlCarrier N) metric a univ (G2.groupRegularize G φ f ε) ≤
        @H2.boundedHolderNorm (ControlCarrier N) metric a univ f) ∧
    (∀ b : ℝ≥0, b < a →
      Tendsto (fun p : ℝ × ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric b univ
        (fun x => G2.groupRegularize G φ f p.1 x - G2.groupRegularize G φ f p.2 x))
        ((𝓝[>] 0) ×ˢ (𝓝[>] 0)) (𝓝 0)) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hb
  refine ⟨eventually_groupRegularize_smooth_same_ball G ν h1 φ hf hc hs,
    G2.tendstoUniformly_groupRegularize G φ hf hc, ?_, ?_⟩
  · intro ε hε
    exact groupRegularize_holderNorm_le G ν h1 hsym φ a hf hε hb
  · intro b hba
    exact tendsto_holderNorm_groupRegularize_cauchy G ν h1 hsym φ ha hba hf hc hb

end RothschildStein.H3
