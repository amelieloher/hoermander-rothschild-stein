-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GroupMollification
public import RothschildStein.H3.FrozenHolderMetricNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal
namespace RothschildStein.H3

/-- Actual group mollification with the fixed control seminorm
and full norm, including two-scale convergence at every lower exponent. -/
theorem group_mollification_in_fixed_control_norm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) (φ : G2.GroupMollifier G C.norm)
    {ρ : ℝ} {a : ℝ≥0} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | C.norm x < ρ})
    (hb : holderENorm (controlDistance univ w X) a univ f < ⊤) :
    (∀ᶠ ε : ℝ in 𝓝[>] 0,
      ContDiff ℝ (⊤ : ℕ∞) (G2.groupRegularize G φ f ε) ∧
      HasCompactSupport (G2.groupRegularize G φ f ε) ∧
      tsupport (G2.groupRegularize G φ f ε) ⊆ {x | C.norm x < ρ}) ∧
    TendstoUniformly (fun ε : ℝ => G2.groupRegularize G φ f ε) f (𝓝[>] 0) ∧
    (∀ ε : ℝ, 0 < ε →
      holderSeminorm (controlDistance univ w X) a univ (G2.groupRegularize G φ f ε) ≤
        holderSeminorm (controlDistance univ w X) a univ f ∧
      holderENorm (controlDistance univ w X) a univ (G2.groupRegularize G φ f ε) ≤
        holderENorm (controlDistance univ w X) a univ f) ∧
    (∀ b : ℝ≥0, b < a →
      Tendsto (fun p : ℝ × ℝ => holderENorm (controlDistance univ w X) b univ
        (fun x => G2.groupRegularize G φ f p.1 x - G2.groupRegularize G φ f p.2 x))
        ((𝓝[>] 0) ×ˢ (𝓝[>] 0)) (𝓝 0)) := by
  have hb' : @H2.BoundedHolder (ControlCarrier N)
      (gaugeMetric G C.norm C.constant_one C.symmetric) a univ f := by
    rw [frozen_holderENorm_eq_control_norm G w X C a univ f] at hb
    exact hb
  obtain ⟨hsmooth, hconv, hbound, hcauchy⟩ := group_mollification
    G C.norm C.constant_one C.symmetric φ ha hf hc hs hb'
  refine ⟨hsmooth, hconv, ?_, ?_⟩
  · intro ε hε
    simp only [frozen_holderSeminorm_eq_control_semi G w X C,
      frozen_holderENorm_eq_control_norm G w X C]
    exact (hbound ε hε).2
  · intro b hba
    simp only [frozen_holderENorm_eq_control_norm G w X C]
    exact hcauchy b hba

end RothschildStein.H3
