-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyBandPacking
public import HeatKernel.Poincare.DyadicRadiusSum

/-! Quantitative radius sums for disjoint radial ball families. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Exact volume and the radial center bound control the sum of radii by twice the
uniform band packing constant times the largest permitted radius. -/
theorem sum_radii_le_of_radial_ball_packing {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (s : Finset ι) (z : ι → E) (a : ι → ℝ) (x : E) {M κ : ℝ}
    (hM : 0 < M) (hκ : 0 ≤ κ + 10) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (z i) (a i))
    (hpos : ∀ i ∈ s, 0 < a i) (hmax : ∀ i ∈ s, a i ≤ M)
    (hcenter : ∀ i ∈ s, dist x (z i) ≤ (κ + 10) * a i) :
    (∑ i ∈ s, a i) ≤ 2 * (k ^ Q : ℕ) * M := by
  classical
  have hband : ∀ i, i ∈ s → ∃ n : ℕ,
      M * (1 / 2 : ℝ) ^ (n + 1) < a i ∧ a i ≤ M * (1 / 2 : ℝ) ^ n :=
    fun i hi => exists_dyadic_radius_band (hpos i hi) hM (hmax i hi)
  choose f hf using hband
  let n : ι → ℕ := fun i => if hi : i ∈ s then f i hi else 0
  have hn : ∀ i ∈ s, M * (1 / 2 : ℝ) ^ (n i + 1) < a i ∧
      a i ≤ M * (1 / 2 : ℝ) ^ n i := by
    intro i hi
    simpa only [n, dite_eq_left hi] using hf i hi
  apply sum_le_of_dyadic_radius_assignment s a n hM.le (by positivity)
    (fun i hi => (hn i hi).2)
  intro j
  let t := s.filter fun i => n i = j
  have hh : 0 < M * (1 / 2 : ℝ) ^ (j + 1) := mul_pos hM (pow_pos (by norm_num) _)
  have hb : t.card ≤ k ^ Q := by
    apply card_le_of_radial_ball_radius_band μ Q v hv0 hvtop hvolume t z a x hh hκ k hk
      hscale
    · intro i hi l hl hil
      exact hdisj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hl).1 hil
    · intro i hi
      obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
      simpa only [hij] using (hn i his).1.le
    · intro i hi
      obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
      have hu := (hn i his).2
      rw [hij] at hu
      rw [pow_succ]
      nlinarith
    · intro i hi
      exact hcenter i (Finset.mem_filter.mp hi).1
  exact_mod_cast hb

end HeatKernel
