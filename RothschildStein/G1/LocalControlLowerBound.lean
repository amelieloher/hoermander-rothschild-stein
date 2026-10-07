-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactPatchControlBalls

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators ENNReal

namespace RothschildStein.G1

/-- A local field bound gives a linear lower bound for the
actual extended control distance near its center. First exit treats curves
which leave the buffer; all positive weights are allowed (BB pp. 20–24,
Propositions 1.37/1.42, and Theorem 1.53, p. 35). -/
theorem ofReal_norm_div_le_controlDistance_of_local_bound {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {x y : Fin n → ℝ} {B R : ℝ} (hB : 0 < B)
    (hnear : ‖y - x‖ ≤ min R B)
    (hbound : ∀ z, ‖z - x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) :
    ENNReal.ofReal (‖y - x‖ / B) ≤ controlDistance Ω w X x y := by
  unfold controlDistance
  apply le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hγ0, hγ1⟩
  apply ENNReal.ofReal_le_ofReal
  by_cases hzero : ‖y - x‖ = 0
  · simp only [hzero, zero_div]
    exact hγ.1.le
  have hpos : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  by_cases hδ : δ ≤ 1
  · apply (div_le_iff₀ hB).mpr
    have he := controlledCurve_firstExit_bound hγ hδ hB.le hpos
      (by simpa only [hγ0, hγ1] using (le_rfl : ‖y - x‖ ≤ ‖y - x‖))
      (fun z hz => hbound z (by
        simpa only [hγ0] using hz.trans (hnear.trans (min_le_left _ _))))
    exact he
  · have h1 : ‖y - x‖ / B ≤ (1 : ℝ) := (div_le_iff₀ hB).mpr (by
      simpa only [one_mul] using hnear.trans (min_le_right _ _))
    exact h1.trans (le_of_not_ge hδ)

/-- Compact centers in an open smooth coefficient domain
have uniform positive near-diagonal lower-comparison constants. This
conclusion does not require bracket rank or finite
distance (BB Theorem 1.53, p. 35; the first-exit estimate). -/
theorem exists_compact_local_control_lower_bound {m n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) :
    ∃ ρ cminus : ℝ, 0 < ρ ∧ 0 < cminus ∧
      ∀ x ∈ K, ∀ y : Fin n → ℝ, ‖y - x‖ < ρ →
        ENNReal.ofReal (cminus * ‖y - x‖) ≤ controlDistance Ω w X x y := by
  obtain ⟨B, R, hB, hR, _hbuffer, hbound⟩ :=
    exists_uniform_control_buffer hK hΩ hKΩ Subset.rfl X hX
  refine ⟨min R B, B⁻¹, lt_min hR hB, inv_pos.mpr hB, ?_⟩
  intro x hx y hy
  simpa only [div_eq_mul_inv, mul_comm] using
    ofReal_norm_div_le_controlDistance_of_local_bound hB hy.le (hbound x hx)

end RothschildStein.G1
