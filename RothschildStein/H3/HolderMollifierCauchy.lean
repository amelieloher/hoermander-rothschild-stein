-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderMollifierConvergence
public import RothschildStein.H2.HolderLinear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.H3

private theorem holderNorm_sub_le_errors {X : Type*} [MetricSpace X]
    (a : ℝ≥0) (u v f : X → ℝ) :
    H2.boundedHolderNorm a univ (fun x => u x - v x) ≤
      H2.boundedHolderNorm a univ (fun x => u x - f x) +
      H2.boundedHolderNorm a univ (fun x => v x - f x) := by
  have hneg := H2.boundedHolderNorm_smul (δ := a) (U := (univ : Set X))
    (-1) (fun x => v x - f x)
  have he : (-1 : ℝ) • (fun x => v x - f x) = (fun x => f x - v x) := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [he] at hneg
  simp only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] at hneg
  have hs := H2.boundedHolderNorm_add_le (δ := a) (G := (univ : Set X))
    (f := fun x => u x - f x) (g := fun x => f x - v x)
  have ha : (fun x => (u x - f x) + (f x - v x)) = (fun x => u x - v x) := by
    funext x; ring
  rwa [ha, hneg] at hs

/-- Actual group mollifier differences tend to zero in the exact
lower Hölder norm as both positive scales tend to zero independently.
BB Theorem 8.52, pp. 381–382; the two-scale Cauchy assertion is the gap fill. -/
theorem tendsto_holderNorm_groupRegularize_cauchy {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (φ : G2.GroupMollifier G ν) {a b : ℝ≥0} (ha : 0 < a) (hba : b < a)
    {f : ControlCarrier N → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    @H2.BoundedHolder (ControlCarrier N) metric a univ f →
    Tendsto (fun p : ℝ × ℝ => @H2.boundedHolderNorm (ControlCarrier N) metric b univ
      (fun x => G2.groupRegularize G φ f p.1 x - G2.groupRegularize G φ f p.2 x))
      ((𝓝[>] 0) ×ˢ (𝓝[>] 0)) (𝓝 0) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hb
  have h := tendsto_holderNorm_groupRegularize_sub G ν h1 hsym φ ha hba hf hc hb
  have hu := (h.comp tendsto_fst).add (h.comp tendsto_snd)
  simp only [zero_add] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => bot_le) (fun p => @holderNorm_sub_le_errors (ControlCarrier N) metric b
      (G2.groupRegularize G φ f p.1 : ControlCarrier N → ℝ)
      (G2.groupRegularize G φ f p.2 : ControlCarrier N → ℝ) f)

end RothschildStein.H3
