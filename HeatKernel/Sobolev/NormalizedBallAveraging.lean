-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalSignedAveraging
import Mathlib.Tactic

/-! # Ball averaging normalized at a reference radius -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Inverse horizontal ball volumes scale by the reciprocal radius ratio. -/
theorem inv_volume_horizontalBall_eq {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 s))⁻¹ =
      ENNReal.ofReal ((r / s) ^ G.homogeneousDimension) *
        (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ := by
  rw [volume_horizontalBall G hq hw 0 hs, volume_horizontalBall G hq hw 0 hr]
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl ENNReal.ofReal_ne_top)]
  rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos (pow_pos hs _),
    ← ENNReal.ofReal_inv_of_pos (pow_pos hr _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [div_pow]
  field_simp

/-- The signed averaging estimate normalized by the volume at any reference radius. -/
theorem eLpNorm_signed_ballAverage_sq_le_normalized {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ^ 2 ≤
      ENNReal.ofReal ((r / s) ^ G.homogeneousDimension) *
        (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
        eLpNorm f 1 (volume G hq hqpos hspan) ^ 2 := by
  simpa only [inv_volume_horizontalBall_eq G hq hw hs hr] using
    eLpNorm_signed_ballAverage_sq_le G hq hqpos hspan hw hs hf

/-- Increasing the dimension exponent gives the subcritical normalized averaging bound. -/
theorem eLpNorm_signed_ballAverage_sq_le_rpow {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {s r ν : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    (hν : (G.homogeneousDimension : ℝ) ≤ ν)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
      MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
      (volume G hq hqpos hspan) ^ 2 ≤
      ENNReal.ofReal ((r / s) ^ ν) *
        (MeasureTheory.volume (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
        eLpNorm f 1 (volume G hq hqpos hspan) ^ 2 := by
  apply (eLpNorm_signed_ballAverage_sq_le_normalized G hq hqpos hspan hw hs
    (hs.trans_le hsr) hf).trans
  gcongr
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le ((one_le_div hs).mpr hsr) hν

end HeatKernel.CarnotPoint
