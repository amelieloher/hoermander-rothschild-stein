-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.SetAverageExtendedOscillation
public import HeatKernel.Sobolev.EnlargedLocalAveragingError
public import HeatKernel.Sobolev.BallAveraging
import Mathlib.Tactic

/-! # Signed ball-averaging error from local Poincaré estimates -/

@[expose] public section
open Set MeasureTheory Metric
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- A ball cover, enlarged overlap bound, and dilated oscillation estimates control
the actual signed averaging error. -/
theorem lintegral_signed_ballAverage_error_le_of_cover_dilated_poincare
    {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [Countable ι] {μ : Measure α}
    (centers : ι → α) {s : ℝ} (hs : 0 < s) {V P K : ℝ≥0∞}
    (hV : V ≠ 0) (hVtop : V ≠ ⊤) (hvolume : ∀ x : α, μ (ball x s) = V)
    (hcover : ⋃ i, ball (centers i) s = univ)
    (hoverlap : ∀ x, ∑' i, (ball (centers i) (16 * s)).indicator
      (fun _ => (1 : ℝ≥0∞)) x ≤ K)
    {f : α → ℝ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf₂ : Integrable (fun x => f x ^ 2) μ) {g : α → ℝ≥0∞} (hg : Measurable g)
    (hpoincare : ∀ i,
      (∫⁻ x in ball (centers i) (4 * s), ENNReal.ofReal ((f x -
        (∫ y in ball (centers i) (4 * s), f y ∂μ) / μ.real (ball (centers i) (4 * s))) ^ 2) ∂μ) ≤
      P * ENNReal.ofReal (4 * s) ^ 2 * ∫⁻ x in ball (centers i) (16 * s), g x ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((f x - (∫ y in ball x s, f y ∂μ) / V.toReal) ^ 2) ∂μ) ≤
      (4 * P * ENNReal.ofReal (4 * s) ^ 2) * K * ∫⁻ x, g x ∂μ := by
  let m : ι → ℝ := fun i => (∫ y in ball (centers i) (4 * s), f y ∂μ) /
    μ.real (ball (centers i) (4 * s))
  have hh (i : ι) : Measurable (fun x => ENNReal.ofReal ((f x - m i) ^ 2)) := by fun_prop
  apply lintegral_average_error_le_of_enlarged_poincare (μ := μ)
    (U := fun i => ball (centers i) s) (W := fun i => ball (centers i) (4 * s))
    (Z := fun i => ball (centers i) (16 * s))
    hcover (fun _ => measurableSet_ball) (fun _ => measurableSet_ball)
    (fun _ => ball_subset_ball (by linarith : s ≤ 4 * s)) hg hh
    (k := ballAverageKernel s V) (c := V⁻¹) (P := P) (s := ENNReal.ofReal (4 * s)) (K := K)
  · intro i x hx y
    unfold ballAverageKernel
    split_ifs <;> simp
  · intro i x hx y hy
    have hnot : ¬dist x y < s := by
      intro hxy
      apply hy
      rw [mem_ball] at hx ⊢
      have htri := dist_triangle y x (centers i)
      rw [dist_comm y x] at htri
      linarith
    simp only [ballAverageKernel, ite_eq_right hnot]
  · intro i
    rw [hvolume, ENNReal.inv_mul_cancel hV hVtop]
  · intro i x hx
    have hpos : 0 < μ.real (ball x s) := by
      change 0 < (μ (ball x s)).toReal
      rw [hvolume x]
      exact ENNReal.toReal_pos hV hVtop
    have H := ofReal_sq_sub_setAverage_le measurableSet_ball hpos
      hfi.restrict hf₂.restrict (f x) (m i)
    simp only [Measure.real, hvolume x] at H
    have he : (fun y => ballAverageKernel s V x y * ENNReal.ofReal ((f y - m i) ^ 2)) =
        (ball x s).indicator (fun y => V⁻¹ * ENNReal.ofReal ((f y - m i) ^ 2)) := by
      funext y
      by_cases hy : dist x y < s <;> simp [ballAverageKernel, indicator, mem_ball, dist_comm, hy]
    rw [he, lintegral_indicator measurableSet_ball, lintegral_const_mul V⁻¹ (hh i)]
    simpa only [mul_assoc] using H
  · exact hpoincare
  · exact hoverlap

end HeatKernel.Sobolev
