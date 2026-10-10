-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! # Buffered cylinders for the parabolic Harnack iteration

The earlier family shares its bottom time and the later family shares its top
time. Their fixed rational parameters place the target cylinders strictly inside
the appropriate logarithmic tail regions.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
namespace HeatKernel

variable {E : Type*} [PseudoMetricSpace E]

/-- The earlier target cylinder of the parabolic Harnack comparison. -/
def harnackEarlierTargetCylinder (x : E) (t r : ℝ) : Set (ℝ × E) :=
  Ioo (t - 3 * r ^ 2) (t - 2 * r ^ 2) ×ˢ Metric.ball x r

/-- The later target cylinder, whose top time agrees with the outer domain. -/
def harnackLaterTargetCylinder (x : E) (t r : ℝ) : Set (ℝ × E) :=
  Ioo (t - r ^ 2) t ×ˢ Metric.ball x r

/-- The bottom-sharing family used for the earlier reverse Hölder estimate. -/
def harnackEarlierIterationCylinder (x : E) (t r σ : ℝ) : Set (ℝ × E) :=
  Ioo (t - 25 / 8 * r ^ 2) (t - 25 / 8 * r ^ 2 + 5 / 4 * σ ^ 2 * r ^ 2) ×ˢ
    Metric.ball x (5 / 4 * σ * r)

/-- The top-sharing family used for the reciprocal mean-value estimate. -/
def harnackLaterIterationCylinder (x : E) (t r σ : ℝ) : Set (ℝ × E) :=
  Ioo (t - 3 / 2 * σ ^ 2 * r ^ 2) t ×ˢ Metric.ball x (5 / 4 * σ * r)

/-- The earlier fixed-exponent mean-value source cylinder. -/
def harnackEarlierSourceCylinder (x : E) (t r : ℝ) : Set (ℝ × E) :=
  Ioo (t - 25 / 8 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ Metric.ball x (6 / 5 * r)

/-- The upper part of the earlier mean-value source. -/
def harnackEarlierUpperCylinder (x : E) (t r : ℝ) : Set (ℝ × E) :=
  Ioo (t - 49 / 16 * r ^ 2) (t - 63 / 32 * r ^ 2) ×ˢ Metric.ball x r

/-- Both iteration families increase with their nonnegative scale parameter. -/
theorem harnackIterationCylinders_mono (x : E) (t : ℝ) {r σ ρ : ℝ}
    (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hσρ : σ ≤ ρ) :
    harnackEarlierIterationCylinder x t r σ ⊆ harnackEarlierIterationCylinder x t r ρ ∧
    harnackLaterIterationCylinder x t r σ ⊆ harnackLaterIterationCylinder x t r ρ := by
  have hs := (sq_le_sq₀ hσ (hσ.trans hσρ)).mpr hσρ
  have hsq := mul_le_mul_of_nonneg_right hs (sq_nonneg r)
  have hb : 5 / 4 * σ * r ≤ 5 / 4 * ρ * r := by nlinarith
  constructor
  · intro z hz
    exact ⟨⟨hz.1.1, by dsimp [harnackEarlierIterationCylinder] at hz ⊢; nlinarith [hz.1.2]⟩,
      Metric.ball_subset_ball hb hz.2⟩
  · intro z hz
    exact ⟨⟨by dsimp [harnackLaterIterationCylinder] at hz ⊢; nlinarith [hz.1.1], hz.1.2⟩,
      Metric.ball_subset_ball hb hz.2⟩

/-- The earlier source fits into the bottom-sharing family at scale 31/32. -/
theorem harnackEarlierSourceCylinder_subset_iteration (x : E) (t : ℝ)
    {r : ℝ} (hr : 0 < r) :
    harnackEarlierSourceCylinder x t r ⊆ harnackEarlierIterationCylinder x t r (31 / 32) := by
  intro z hz
  refine ⟨⟨hz.1.1, ?_⟩, Metric.ball_subset_ball (by nlinarith : 6 / 5 * r ≤ 5 / 4 * (31 / 32) * r) hz.2⟩
  dsimp [harnackEarlierSourceCylinder, harnackEarlierIterationCylinder] at hz ⊢
  nlinarith [hz.1.2, sq_pos_of_pos hr]

/-- The earlier target lies inside the upper part of the mean-value source. -/
theorem harnackEarlierTargetCylinder_subset_upper (x : E) (t r : ℝ) :
    harnackEarlierTargetCylinder x t r ⊆ harnackEarlierUpperCylinder x t r := by
  intro z hz
  refine ⟨⟨?_, ?_⟩, hz.2⟩
  · dsimp [harnackEarlierTargetCylinder, harnackEarlierUpperCylinder] at hz ⊢
    nlinarith [hz.1.1, sq_nonneg r]
  · dsimp [harnackEarlierTargetCylinder, harnackEarlierUpperCylinder] at hz ⊢
    nlinarith [hz.1.2, sq_nonneg r]

/-- The upper mean-value cylinder has a fixed positive bottom and spatial buffer. -/
theorem harnackEarlierUpperCylinder_subset_source (x : E) (t : ℝ)
    {r : ℝ} (hr : 0 < r) :
    harnackEarlierUpperCylinder x t r ⊆ harnackEarlierSourceCylinder x t r := by
  intro z hz
  refine ⟨⟨?_, hz.1.2⟩, Metric.ball_subset_ball (by linarith : r ≤ 6 / 5 * r) hz.2⟩
  dsimp [harnackEarlierUpperCylinder, harnackEarlierSourceCylinder] at hz ⊢
  nlinarith [hz.1.1, sq_pos_of_pos hr]

/-- The later target fits inside the reciprocal iteration family at scale 9/10. -/
theorem harnackLaterTargetCylinder_subset_iteration (x : E) (t : ℝ)
    {r : ℝ} (hr : 0 < r) :
    harnackLaterTargetCylinder x t r ⊆ harnackLaterIterationCylinder x t r (9 / 10) := by
  intro z hz
  refine ⟨⟨?_, hz.1.2⟩, Metric.ball_subset_ball (by linarith : r ≤ 5 / 4 * (9 / 10) * r) hz.2⟩
  dsimp [harnackLaterTargetCylinder, harnackLaterIterationCylinder] at hz ⊢
  nlinarith [hz.1.1, sq_pos_of_pos hr]

/-- The outer earlier family lies strictly before every allowed separating time. -/
theorem harnackEarlierIterationCylinder_subset_logarithmic_region (x : E) (t : ℝ)
    {r τ : ℝ} (hτ : t - 113 / 64 * r ^ 2 < τ) :
    harnackEarlierIterationCylinder x t r 1 ⊆
      Ioo (t - 225 / 64 * r ^ 2) τ ×ˢ Metric.ball x (5 / 4 * r) := by
  intro z hz
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp [harnackEarlierIterationCylinder] at hz
    nlinarith [hz.1.1, sq_nonneg r]
  · dsimp [harnackEarlierIterationCylinder] at hz
    nlinarith [hz.1.2, sq_nonneg r]
  · simpa only [mul_one] using hz.2

/-- The outer later family lies strictly after every allowed separating time. -/
theorem harnackLaterIterationCylinder_subset_logarithmic_region (x : E) (t : ℝ)
    {r τ : ℝ} (hτ : τ < t - 111 / 64 * r ^ 2) :
    harnackLaterIterationCylinder x t r 1 ⊆ Ioo τ t ×ˢ Metric.ball x (5 / 4 * r) := by
  intro z hz
  refine ⟨⟨?_, hz.1.2⟩, ?_⟩
  · dsimp [harnackLaterIterationCylinder] at hz
    nlinarith [hz.1.1, sq_nonneg r]
  · simpa only [mul_one] using hz.2

end HeatKernel
