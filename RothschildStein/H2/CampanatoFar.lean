-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The exact far-distance constant C(b). -/
def campanatoFarConstant (P : DoublingPatch X) (α : ℝ) : ℝ :=
  2 * max ((1 + campanatoTailConstant P α) * (2 : ℝ) ^ α)
    ((3 * P.ρ) ^ (-α) / campanatoMinVolume P)

/-- Far-distance Hölder estimate (7.30), retaining the outer L¹ norm
as required by BB Remark 7.39 (pp. 327 and 331). -/
theorem campanatoRepresentative_far (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x y : X}
    (hx : x ∈ P.S) (hy : y ∈ P.S) (hxy : 3 * P.ρ < dist x y) :
    |campanatoRepresentative P α u x - campanatoRepresentative P α u y| ≤
      campanatoFarConstant P α * ((campanatoSeminorm α P u).toReal +
        (∫ z in P.W, |u z| ∂P.μ)) * dist x y ^ α := by
  let A := (1 + campanatoTailConstant P α) * (2 : ℝ) ^ α
  let B := (3 * P.ρ) ^ (-α) / campanatoMinVolume P
  let C := max A B
  have hρ : 0 < 3 * P.ρ := by linarith [P.ρ_pos]
  have hd : 0 ≤ dist x y := dist_nonneg
  have hp := Real.rpow_le_rpow hρ.le hxy.le hα.le
  have ht := campanatoTailConstant_pos P hα
  have hm := campanatoMinVolume_pos P hx
  have h6 : (6 * P.ρ) ^ α = (2 : ℝ) ^ α * (3 * P.ρ) ^ α := by
    rw [show 6 * P.ρ = 2 * (3 * P.ρ) by ring, Real.mul_rpow (by norm_num) hρ.le]
  have hA : (1 + campanatoTailConstant P α) * (6 * P.ρ) ^ α ≤ C * dist x y ^ α := by
    rw [h6, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_left hp (mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) α))).trans
      (mul_le_mul_of_nonneg_right (le_max_left A B) (Real.rpow_nonneg hd α))
  have he : (3 * P.ρ) ^ (-α) * (3 * P.ρ) ^ α = 1 := by
    rw [Real.rpow_neg hρ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hρ α).ne']
  have hB : 1 / campanatoMinVolume P ≤ C * dist x y ^ α := by
    have hh := mul_le_mul_of_nonneg_left hp
      (div_nonneg (Real.rpow_nonneg hρ.le (-α)) hm.le)
    have hh' : 1 / campanatoMinVolume P ≤ B * dist x y ^ α := by
      dsimp [B] at hh ⊢
      have heq : (3 * P.ρ) ^ (-α) / campanatoMinVolume P * (3 * P.ρ) ^ α =
          1 / campanatoMinVolume P := by rw [div_mul_eq_mul_div, he]
      rwa [heq] at hh
    exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.rpow_nonneg hd α))
  have hxB := campanatoRepresentative_uniform_abs P hα hu hx
  have hyB := campanatoRepresentative_uniform_abs P hα hu hy
  have htri := abs_sub_le (campanatoRepresentative P α u x) 0 (campanatoRepresentative P α u y)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have hAM := mul_le_mul_of_nonneg_right hA (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u))
  have hBI := mul_le_mul_of_nonneg_right hB
    (integral_nonneg (μ := P.μ.restrict P.W) fun z => abs_nonneg (u z))
  change _ ≤ 2 * C * _ * _
  have heq : (∫ z in P.W, |u z| ∂P.μ) / campanatoMinVolume P =
      (1 / campanatoMinVolume P) * (∫ z in P.W, |u z| ∂P.μ) := by ring
  rw [heq] at hxB hyB
  nlinarith
end RothschildStein.H2
