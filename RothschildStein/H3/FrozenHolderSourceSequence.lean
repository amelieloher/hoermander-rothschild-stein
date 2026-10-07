-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FixedNormMollification
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal
namespace RothschildStein.H3

/-- Actual group mollification supplies a sequence of smooth
sources with the same compact support buffer, a common full Hölder bound,
and two-index convergence of differences at every lower exponent. -/
theorem exists_fixed_holder_source_sequence_of_controlNorm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) (φ : G2.GroupMollifier G C.norm)
    {ρ : ℝ} {a : ℝ≥0} (ha : 0 < a)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | C.norm x < ρ})
    (hb : holderENorm (controlDistance univ w X) a univ f < ⊤) :
    ∃ F : ℕ → (Fin N → ℝ) → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n) ∧ HasCompactSupport (F n) ∧
        tsupport (F n) ⊆ {x | C.norm x < ρ}) ∧
      TendstoUniformly F f atTop ∧
      (∀ n, holderENorm (controlDistance univ w X) a univ (F n) ≤
        holderENorm (controlDistance univ w X) a univ f) ∧
      (∀ b : ℝ≥0, b < a → Tendsto (fun p : ℕ × ℕ =>
        holderENorm (controlDistance univ w X) b univ (fun x => F p.1 x - F p.2 x))
        (atTop ×ˢ atTop) (𝓝 0)) := by
  obtain ⟨hsmooth, hconv, hbound, hdiff⟩ :=
    group_mollification_in_fixed_control_norm G w X C φ ha hf hc hs hb
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have ht : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (ht.eventually hsmooth)
  let e := fun n => ε (n + n₀)
  have he : Tendsto e atTop (𝓝[>] 0) := ht.comp (tendsto_add_atTop_nat n₀)
  refine ⟨fun n => G2.groupRegularize G φ f (e n), ?_, ?_, ?_, ?_⟩
  · intro n
    exact hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  · intro u hu
    exact he.eventually (hconv u hu)
  · intro n
    exact (hbound (e n) (hpos (n + n₀))).2
  · intro b hba
    have hpair : Tendsto (Prod.map e e) (atTop ×ˢ atTop)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) := he.prodMap he
    have hlimit := (hdiff b hba).comp hpair
    exact hlimit

end RothschildStein.H3
