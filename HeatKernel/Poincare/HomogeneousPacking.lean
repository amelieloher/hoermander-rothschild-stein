-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.DisjointPacking
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Tactic.Positivity

/-! Exact polynomial packing bounds from homogeneous ball volumes. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- In an exact homogeneous-volume metric space, disjoint balls of radius at least h
contained in a ball of radius kh have cardinality at most k^Q. -/
theorem card_le_of_homogeneous_ball_packing {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (s : Finset ι) (z : ι → E) (a : ι → ℝ) (x : E) {h : ℝ} (hh : 0 < h)
    (k : ℕ) (hk : 0 < k)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (z i) (a i))
    (hlower : ∀ i ∈ s, h ≤ a i)
    (hsub : ∀ i ∈ s, ball (z i) (a i) ⊆ ball x ((k : ℝ) * h)) : s.card ≤ k ^ Q := by
  let c := ENNReal.ofReal (h ^ Q) * v
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos hh Q)).ne' hv0
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvtop
  have hmass : ∀ i ∈ s, c ≤ μ (ball (z i) (a i)) := by
    intro i hi
    rw [hvolume (z i) (a i) (hh.trans_le (hlower i hi))]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hh.le (hlower i hi) Q)) v
  have hU : μ (ball x ((k : ℝ) * h)) ≤ (k ^ Q : ℕ) * c := by
    rw [hvolume x ((k : ℝ) * h) (mul_pos (by exact_mod_cast hk) hh), mul_pow,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    simp only [Nat.cast_pow, c, mul_assoc]
    exact le_rfl
  exact card_le_of_disjoint_measure_bound μ s hdisj (fun _ _ => isOpen_ball.measurableSet)
    hsub hmass hc0 hctop hU

/-- The same homogeneous-volume bound forces an arbitrary disjoint packing with a
uniform positive lower radius to be finite. -/
theorem finite_of_homogeneous_ball_packing {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    {I : Set ι} (z : ι → E) (a : ι → ℝ) (x : E) {h : ℝ} (hh : 0 < h)
    (k : ℕ) (hk : 0 < k) (hdisj : I.PairwiseDisjoint fun i => ball (z i) (a i))
    (hlower : ∀ i ∈ I, h ≤ a i)
    (hsub : ∀ i ∈ I, ball (z i) (a i) ⊆ ball x ((k : ℝ) * h)) : I.Finite := by
  classical
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (k ^ Q + 1)
  have hb := card_le_of_homogeneous_ball_packing μ Q v hv0 hvtop hvolume s z a x hh k hk
    (fun _ hi _ hj hij => hdisj (hs hi) (hs hj) hij)
    (fun i hi => hlower i (hs hi)) (fun i hi => hsub i (hs hi))
  exact (Nat.lt_succ_self (k ^ Q)).not_ge (by simpa only [hcard] using hb)

end HeatKernel
