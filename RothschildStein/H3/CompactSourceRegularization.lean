-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierExistence
public import RothschildStein.G2.MollifierSmooth
public import RothschildStein.G2.MollifierLpConvergence
public import RothschildStein.G2.ConvolutionSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N) {ν : G2.HomogeneousNorm G}

/-- Mollification enlarges a gauge support radius by at most its scale. -/
theorem groupRegularize_vanish_outside_radius (φ : G2.GroupMollifier G ν)
    (hν : ν.c = 1) {σ ε : ℝ} (hε : 0 < ε)
    {f : (Fin N → ℝ) → ℝ} (hf : ∀ x, σ ≤ ν x → f x = 0) :
    ∀ x, σ + ε ≤ ν x → G2.groupRegularize G φ f ε x = 0 := by
  intro x hx
  by_contra hn
  have hs := G2.support_groupConvolution_subset G
    (G2.groupMollifierScale G φ ε) f hn
  rcases hs with ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
  have hna : ν a < ε := G2.support_groupMollifierScale_subset G φ hε ha
  have hnb : ν b < σ := lt_of_not_ge fun h => hb (hf b h)
  have ht := ν.mul_le a b
  rw [hν, one_mul] at ht
  linarith

/-- Compact Lp sources have smooth compact regularizations converging in Lp,
with a common enlarged gauge support radius. -/
theorem compact_source_regularization (φ : G2.GroupMollifier G ν)
    (hν : ν.c = 1) {σ p : ℝ} (hp : 1 ≤ p)
    {f : (Fin N → ℝ) → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hcf : HasCompactSupport f) (hs : ∀ x, σ ≤ ν x → f x = 0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ContDiff ℝ (⊤ : ℕ∞) (G2.groupRegularize G φ f ε) ∧
      HasCompactSupport (G2.groupRegularize G φ f ε) ∧
      ∀ x, σ + 1 ≤ ν x → G2.groupRegularize G φ f ε x = 0) ∧
    Tendsto (fun ε : ℝ => eLpNorm (G2.groupRegularize G φ f ε - f)
      (ENNReal.ofReal p) volume) (𝓝[>] 0) (𝓝 0) := by
  refine ⟨?_, G2.tendsto_groupRegularize_eLpNorm G φ hp hf⟩
  intro ε hε he
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  obtain ⟨ha, hb⟩ := G2.contDiff_hasCompactSupport_groupRegularize G φ hε hpE hf hcf
  refine ⟨ha, hb, ?_⟩
  intro x hx
  exact groupRegularize_vanish_outside_radius G φ hν hε hs x (by linarith)

end RothschildStein.H3
