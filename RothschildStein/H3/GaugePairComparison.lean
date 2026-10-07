-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- Two actual homogeneous norms have positive global
comparison constants, by the proved comparison with the maximum gauge. -/
theorem exists_gauge_pair_comparison {n : ℕ} {G : HomogeneousGroup n}
    (ν μ : G2.HomogeneousNorm G) :
    ∃ a B : ℝ, 0 < a ∧ 0 < B ∧ ∀ z, a * ν z ≤ μ z ∧ μ z ≤ B * ν z := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hν⟩ := G2.gauge_equivalent_max ν.gauge
  obtain ⟨a₂, b₂, ha₂, hb₂, hμ⟩ := G2.gauge_equivalent_max μ.gauge
  refine ⟨a₂ / b₁, b₂ / a₁, div_pos ha₂ hb₁, div_pos hb₂ ha₁, ?_⟩
  intro z
  constructor
  · calc
      _ ≤ (a₂ / b₁) * (b₁ * rsGauge G.weight G.weight_pos z) :=
        mul_le_mul_of_nonneg_left (hν z).2 (div_nonneg ha₂.le hb₁.le)
      _ = a₂ * rsGauge G.weight G.weight_pos z := by field_simp [hb₁.ne']
      _ ≤ _ := (hμ z).1
  · calc
      _ ≤ b₂ * rsGauge G.weight G.weight_pos z := (hμ z).2
      _ = (b₂ / a₁) * (a₁ * rsGauge G.weight G.weight_pos z) := by field_simp [ha₁.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hν z).1 (div_nonneg hb₂.le ha₁.le)

end RothschildStein.H3
