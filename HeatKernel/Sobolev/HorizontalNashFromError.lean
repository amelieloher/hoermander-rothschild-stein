-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.HorizontalAverageLp
public import HeatKernel.Sobolev.NashFromAveraging
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Local Nash estimates from signed averaging errors -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Signed averaging errors and normalized moment bounds imply a local Nash estimate.
The scalar parameters bound the normalized energy and first moment explicitly. -/
theorem norm_sq_le_nash_of_signed_average_error {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r K e C D W E ν : ℝ} (hr : 0 < r) (hC : 1 ≤ C)
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hν : 0 < ν)
    (hQ : (G.homogeneousDimension : ℝ) ≤ ν)
    {f : CarnotPoint G hq hqpos hspan → ℝ} (hf : Measurable f)
    (hf₁ : MemLp f 1 (volume G hq hqpos hspan))
    (hf₂ : MemLp f 2 (volume G hq hqpos hspan))
    (herrors : ∀ (s : ℝ), 0 < s →
      (eLpNorm (fun x => f x - (∫ y in ball x s, f y ∂volume G hq hqpos hspan) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 s)) 2
          (volume G hq hqpos hspan)).toReal ^ 2 ≤ K * s ^ 2 * e)
    (herror : K * r ^ 2 * e ≤ C ^ 2 * D ^ 2)
    (hmoment : (MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 r))⁻¹ *
      (eLpNorm f 1 (volume G hq hqpos hspan)).toReal ^ 2 ≤ W ^ 2)
    (henergy : D ^ 2 + ‖hf₂.toLp f‖ ^ 2 ≤ E) :
    ‖hf₂.toLp f‖ ^ 2 ≤ ((C + 1) ^ 2 * 2 ^ (ν / (ν + 2))) *
      E ^ (ν / (ν + 2)) * W ^ (4 / (ν + 2)) := by
  have hzero : W = 0 → ‖hf₂.toLp f‖ = 0 := by
    intro hWzero
    have hv : 0 < MeasureTheory.volume.real
        (horizontalBall (G.horizontalFields hq) 0 r) :=
      ENNReal.toReal_pos (volume_horizontalBall_pos G hq hqpos hspan 0 hr).ne'
        (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 hr.le).ne
    have hm := hmoment
    rw [hWzero] at hm
    have hz : (eLpNorm f 1 (volume G hq hqpos hspan)).toReal = 0 := by
      have hsq : (eLpNorm f 1 (volume G hq hqpos hspan)).toReal ^ 2 ≤ 0 :=
        (mul_le_mul_iff_of_pos_left (inv_pos.mpr hv)).mp (by simpa only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hm)
      nlinarith
    have hnorm : eLpNorm f 1 (volume G hq hqpos hspan) = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right hf₁.eLpNorm_ne_top
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (1 : ℝ≥0∞) ≠ 0)).mp hnorm
    rw [Lp.norm_toLp, eLpNorm_congr_ae hae]
    simp
  apply Sobolev.sq_le_nash_of_unit_radius_bound (norm_nonneg _) hC hD hW hν henergy hzero
  intro t ht ht₁
  have hs : 0 < r * t := mul_pos hr ht
  have hsr : r * t ≤ r := by nlinarith
  obtain ⟨v, hv, hvnorm⟩ := exists_lp_signed_ballAverage G hq hqpos hspan hw hs hsr hQ hf hf₁
  have havg : ‖v‖ ≤ W * t ^ (-ν / 2) := by
    apply hvnorm.trans
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg hW (Real.rpow_nonneg ht.le _), ?_⟩
    have hratio : r / (r * t) = t⁻¹ := by field_simp
    rw [hratio, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, mul_pow,
      ← Real.rpow_mul_natCast ht.le]
    norm_num only [Nat.cast_ofNat]
    have hexp : -ν / 2 * 2 = -ν := by ring
    rw [hexp]
    have h := mul_le_mul_of_nonneg_right hmoment (Real.rpow_nonneg ht.le (-ν))
    convert h using 1; ring
  have herr := herrors (r * t) hs
  have heq : ⇑(hf₂.toLp f - v) =ᵐ[volume G hq hqpos hspan]
      fun x => f x - (∫ y in ball x (r * t), f y ∂volume G hq hqpos hspan) /
        MeasureTheory.volume.real (horizontalBall (G.horizontalFields hq) 0 (r * t)) :=
    (Lp.coeFn_sub _ _).trans (hf₂.coeFn_toLp.sub hv)
  have hn : ‖hf₂.toLp f - v‖ ^ 2 ≤
      K * (r * t) ^ 2 * e := by
    rw [Lp.norm_def, eLpNorm_congr_ae heq]
    exact herr
  have hsq : ‖hf₂.toLp f - v‖ ^ 2 ≤ (C * t * D) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right herror (sq_nonneg t)
    nlinarith [hn]
  have he : ‖hf₂.toLp f - v‖ ≤ C * t * D := by
    have hC₀ : 0 ≤ C := by linarith
    nlinarith [norm_nonneg (hf₂.toLp f - v), mul_nonneg (mul_nonneg hC₀ ht.le) hD]
  calc
    ‖hf₂.toLp f‖ = ‖(hf₂.toLp f - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ ‖hf₂.toLp f - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ C * t * D + W * t ^ (-ν / 2) := add_le_add he havg

end HeatKernel.CarnotPoint
