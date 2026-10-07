-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactSourceRegularization
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Compact support inside an open gauge sublevel has a strict
inner support radius (BB Theorem 8.52, p. 381). -/
theorem exists_inner_support_radius (ν : G2.HomogeneousNorm G)
    {ρ : ℝ} {f : (Fin N → ℝ) → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ν x < ρ}) :
    ∃ σ < ρ, ∀ x, σ ≤ ν x → f x = 0 := by
  classical
  by_cases hn : (tsupport f).Nonempty
  · obtain ⟨x, hx, hm⟩ := hc.exists_isMaxOn hn ν.gauge.1.continuousOn
    refine ⟨(ν x + ρ) / 2, by have := hs hx; dsimp at this; linarith, ?_⟩
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hyt
    have hmax : ν y ≤ ν x := hm hyt
    have hxr : ν x < ρ := hs hx
    linarith
  · refine ⟨ρ - 1, by linarith, fun x _ => image_eq_zero_of_notMem_tsupport ?_⟩
    exact fun hx => hn ⟨x, hx⟩

/-- The actual mollifier is smooth and compactly supported in
 the same open gauge ball at every sufficiently small positive scale.
BB Theorem 8.52, p. 381; compactness supplies the strict support margin. -/
theorem eventually_groupRegularize_smooth_same_ball
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1)
    (φ : G2.GroupMollifier G ν) {ρ : ℝ} {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ν x < ρ}) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ContDiff ℝ (⊤ : ℕ∞) (G2.groupRegularize G φ f ε) ∧
      HasCompactSupport (G2.groupRegularize G φ f ε) ∧
      tsupport (G2.groupRegularize G φ f ε) ⊆ {x | ν x < ρ} := by
  obtain ⟨σ, hσ, hzero⟩ := exists_inner_support_radius G ν hc hs
  have hm : 0 < (ρ - σ) / 2 := by linarith
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 ((ρ - σ) / 2) := Ioo_mem_nhdsGT hm
  filter_upwards [hsmall] with ε he
  have hLp : MemLp f (1 : ℝ≥0∞) volume := hf.memLp_of_hasCompactSupport hc
  obtain ⟨ha, hb⟩ := G2.contDiff_hasCompactSupport_groupRegularize G φ he.1 le_rfl hLp hc
  refine ⟨ha, hb, ?_⟩
  have hz := groupRegularize_vanish_outside_radius G φ h1 he.1 hzero
  have hsupp : Function.support (G2.groupRegularize G φ f ε) ⊆ {x | ν x ≤ σ + ε} := by
    intro x hx
    exact le_of_lt (lt_of_not_ge fun hh => hx (hz x hh))
  have ht : tsupport (G2.groupRegularize G φ f ε) ⊆ {x | ν x ≤ σ + ε} :=
    closure_minimal hsupp (isClosed_le ν.gauge.1 continuous_const)
  intro x hx
  have hh := ht hx
  dsimp at hh ⊢
  linarith [he.2]

end RothschildStein.H3
