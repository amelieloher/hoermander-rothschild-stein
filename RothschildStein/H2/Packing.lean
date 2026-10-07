-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.BallMeasures
public import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Sharp finite packing count from local doubling, replacing BB Prop 7.46,
pp. 332–333. No compactness is used in this count. -/
theorem DoublingPatch.packing (P : DoublingPatch X) (J : Finset X) {x : X}
    {r lam : ℝ} (hr : 0 < r) (hrρ : r ≤ 2 * P.ρ) (hlam : (1 / 2 : ℝ) ≤ lam)
    (hJ : ∀ z ∈ J, z ∈ P.S ∧ z ∈ ball x r)
    (hsep : ∀ z ∈ J, ∀ w ∈ J, z ≠ w → r / lam ≤ dist z w) :
    (J.card : ℝ≥0∞) ≤ ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (6 * lam)⌉₊ := by
  classical
  by_cases hne : J.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    have hlamp : 0 < lam := by linarith
    let s := r / (2 * lam)
    have hs : 0 < s := by dsimp [s]; positivity
    have hsr : s ≤ r := by
      dsimp [s]; apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr; nlinarith
    have houter (z : X) (hz : z ∈ J) : ball x (2 * r) ⊆ ball z (3 * r) := by
      intro y hy
      have hzx := (hJ z hz).2
      rw [mem_ball] at hy hzx ⊢
      have := dist_triangle y x z
      rw [dist_comm x z] at this
      linarith
    have hinner (z : X) (hz : z ∈ J) : ball z s ⊆ ball x (2 * r) := by
      intro y hy
      have hzx := (hJ z hz).2
      rw [mem_ball] at hy hzx ⊢
      have := dist_triangle y z x
      linarith
    have hdisj : (J : Set X).PairwiseDisjoint (fun z => ball z s) := by
      intro z hz w hw hzw
      apply Set.disjoint_left.mpr
      intro y hyz hyw
      rw [mem_ball] at hyz hyw
      have ht := dist_triangle z y w
      rw [dist_comm z y] at ht
      have hsp := hsep z hz w hw hzw
      have he : 2 * s = r / lam := by dsimp [s]; field_simp
      linarith
    have hvp : 0 < P.μ (ball x (2 * r)) :=
      ((P.doubling z₀ (hJ z₀ hz₀).1 s hs (by linarith)).1).trans_le
        (measure_mono (hinner z₀ hz₀))
    have hvf : P.μ (ball x (2 * r)) < ⊤ :=
      lt_of_le_of_lt (measure_mono (houter z₀ hz₀))
        (P.doubling z₀ (hJ z₀ hz₀).1 (3 * r) (by positivity) (by linarith)).2.1
    let A := ENNReal.ofReal P.C_D ^ ⌈Real.logb 2 (6 * lam)⌉₊
    have hcompare (z : X) (hz : z ∈ J) :
        P.μ (ball x (2 * r)) ≤ A * P.μ (ball z s) := by
      have he : (3 * r) / s = 6 * lam := by dsimp [s]; field_simp; ring
      have hb := P.compare (hJ z hz).1 hs (by linarith : s ≤ 3 * r)
        (by linarith : 3 * r ≤ 6 * P.ρ)
      rw [he] at hb
      exact (measure_mono (houter z hz)).trans hb
    have hsum : (J.card : ℝ≥0∞) * P.μ (ball x (2 * r)) ≤
        A * P.μ (ball x (2 * r)) := by
      calc
        _ = ∑ _z ∈ J, P.μ (ball x (2 * r)) := by simp
        _ ≤ ∑ z ∈ J, A * P.μ (ball z s) := Finset.sum_le_sum hcompare
        _ = A * P.μ (⋃ z ∈ J, ball z s) := by
          rw [← Finset.mul_sum, measure_biUnion_finset hdisj (fun _ _ => isOpen_ball.measurableSet)]
        _ ≤ A * P.μ (ball x (2 * r)) :=
          mul_le_mul_right (measure_mono (iUnion₂_subset hinner)) _
    exact (ENNReal.mul_le_mul_iff_left (ne_of_gt hvp) (ne_of_lt hvf)).mp hsum
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- The packing count with real-valued radii. -/
theorem DoublingPatch.packing_card (P : DoublingPatch X) (J : Finset X) {x : X}
    {r lam : ℝ} (hr : 0 < r) (hrρ : r ≤ 2 * P.ρ) (hlam : (1 / 2 : ℝ) ≤ lam)
    (hJ : ∀ z ∈ J, z ∈ P.S ∧ z ∈ ball x r)
    (hsep : ∀ z ∈ J, ∀ w ∈ J, z ≠ w → r / lam ≤ dist z w) :
    (J.card : ℝ) ≤ P.C_D ^ ⌈Real.logb 2 (6 * lam)⌉₊ := by
  have hp : 0 ≤ P.C_D := by linarith [P.one_lt_C_D]
  have hb := P.packing J hr hrρ hlam hJ hsep
  rw [← ENNReal.ofReal_pow hp, ← ENNReal.ofReal_natCast] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hp _)).mp hb

end RothschildStein.H2
