-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Quasidistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- Gauge equivalence gives one control-norm buffer radius
for every center and every local radius bounded by a prescribed maximum.
The buffer is fixed before the input and the cutoff are chosen. -/
theorem exists_uniform_gauge_ball_buffer {N : ℕ} (G : HomogeneousGroup N)
    (ν μ : G2.HomogeneousNorm G) {R : ℝ} (hR : 0 < R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Fin N → ℝ, ∀ s : ℝ, s ≤ R →
      G2.gaugeBall G ν z s ⊆ G2.gaugeBall G μ z ρ := by
  obtain ⟨a, b, _ha, hb, hbound⟩ := G2.gauges_equivalent ν.gauge μ.gauge
  refine ⟨b * R, mul_pos hb hR, ?_⟩
  intro z s hs x hx
  change μ (G.mul (G.inv z) x) < b * R
  change ν (G.mul (G.inv z) x) < s at hx
  exact ((hbound _).2.trans_lt (mul_lt_mul_of_pos_left hx hb)).trans_le
    (mul_le_mul_of_nonneg_left hs hb.le)

end RothschildStein.H3
