-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-!
# Integration of two power bounds on distribution functions

Splitting the layer-cake integral at a positive threshold converts two weak
power estimates into a finite moment. This calculation does not use an operator
interpolation theorem.
-/

@[expose] public section

open MeasureTheory Set

namespace HeatKernel.Sobolev

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Integrating two distribution bounds, on opposite sides of a threshold. -/
theorem lintegral_le_of_two_power_tail_bounds {f : α → ℝ}
    (hf : AEMeasurable f μ) (hf₀ : 0 ≤ᵐ[μ] f)
    {a b A B T : ℝ} (ha : a < 1) (hb : 1 < b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T)
    (hlow : ∀ t, 0 < t → t ≤ T → μ {x | t < f x} ≤ ENNReal.ofReal (A * t ^ (-a)))
    (hhigh : ∀ t, T < t → μ {x | t < f x} ≤ ENNReal.ofReal (B * t ^ (-b))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (A * T ^ (1 - a) / (1 - a)) +
        ENNReal.ofReal (B * T ^ (1 - b) / (b - 1)) := by
  rw [lintegral_eq_lintegral_meas_lt μ hf₀ hf]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      rcases le_or_gt t T with htT | htT
      · exact Or.inl ⟨ht, htT⟩
      · exact Or.inr htT
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hT.trans ht
  rw [hsplit, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (A * t ^ (-a)) :=
        setLIntegral_mono' measurableSet_Ioc (fun t ht => hlow t ht.1 ht.2)
      _ = ENNReal.ofReal (A * T ^ (1 - a) / (1 - a)) := by
        have hi : IntegrableOn (fun t : ℝ => t ^ (-a)) (Ioc 0 T) :=
          (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -a)).1
        rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul A)]
        · rw [integral_const_mul, ← intervalIntegral.integral_of_le hT.le,
            integral_rpow (Or.inl (by linarith : -1 < -a))]
          simp only [show -a + 1 = 1 - a by ring,
            Real.zero_rpow (by linarith : 1 - a ≠ 0), sub_zero]
          congr 1
          ring
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact mul_nonneg hA (Real.rpow_nonneg ht.1.le _)
  · calc
      _ ≤ ∫⁻ t in Ioi T, ENNReal.ofReal (B * t ^ (-b)) :=
        setLIntegral_mono' measurableSet_Ioi (fun t ht => hhigh t ht)
      _ = ENNReal.ofReal (B * T ^ (1 - b) / (b - 1)) := by
        have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -b < -1) hT
        rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul B)]
        · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -b < -1) hT]
          simp only [show -b + 1 = 1 - b by ring]
          congr 1
          have hden : 1 - b = -(b - 1) := by ring
          rw [hden, div_neg]
          ring
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg hB (Real.rpow_nonneg (hT.trans ht).le _)

/-- Two weak power bounds imply a strong intermediate moment, at every threshold. -/
theorem lintegral_abs_rpow_le_of_tail_bounds {u : α → ℝ}
    (hu : AEMeasurable u μ) {l q p A B T : ℝ}
    (hq : 0 < q) (hlq : l < q) (hqp : q < p)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 < T)
    (hlow : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (A * s ^ (-l)))
    (hhigh : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (B * s ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) ≤
      ENNReal.ofReal (A * T ^ (1 - l / q) / (1 - l / q)) +
        ENNReal.ofReal (B * T ^ (1 - p / q) / (p / q - 1)) := by
  have htail (t : ℝ) (ht : 0 < t) :
      {x | t < |u x| ^ q} = {x | t ^ q⁻¹ < |u x|} := by
    ext x
    change t < |u x| ^ q ↔ t ^ q⁻¹ < |u x|
    conv_lhs => rw [← Real.rpow_inv_rpow ht.le hq.ne']
    exact Real.rpow_lt_rpow_iff (Real.rpow_nonneg ht.le _) (abs_nonneg _) hq
  apply lintegral_le_of_two_power_tail_bounds ((by simpa only [Real.norm_eq_abs] using hu.norm :
      AEMeasurable (fun x => |u x|) μ).pow_const q)
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) _))
    ((div_lt_one hq).mpr hlq) ((one_lt_div hq).mpr hqp) hA hB hT
  · intro t ht _
    rw [htail t ht]
    convert hlow (t ^ q⁻¹) (Real.rpow_pos_of_pos ht _) using 1
    simp only [← Real.rpow_mul ht.le, div_eq_mul_inv]
    ring_nf
  · intro t ht
    have ht₀ := hT.trans ht
    rw [htail t ht₀]
    convert hhigh (t ^ q⁻¹) (Real.rpow_pos_of_pos ht₀ _) using 1
    simp only [← Real.rpow_mul ht₀.le, div_eq_mul_inv]
    ring_nf

/-- An integrable positive moment bounds the distribution function. -/
theorem measure_abs_gt_le_integral_rpow {u : α → ℝ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s)
    (hu : Integrable (fun x => |u x| ^ r) μ) :
    μ {x | s < |u x|} ≤ ENNReal.ofReal ((∫ x, |u x| ^ r ∂μ) * s ^ (-r)) := by
  have hnonneg : ∀ x, 0 ≤ |u x| ^ r := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hmeasure : μ {x | s < |u x|} ≤
      μ {x | ENNReal.ofReal (s ^ r) ≤ ENNReal.ofReal (|u x| ^ r)} := by
    apply measure_mono
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hs.le hx.le hr.le)
  have h := meas_ge_le_lintegral_div hu.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hs r)).ne'
    ENNReal.ofReal_ne_top
  apply hmeasure.trans
  rw [← ofReal_integral_eq_lintegral_ofReal hu (Filter.Eventually.of_forall hnonneg),
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hs r)] at h
  convert h using 1
  rw [Real.rpow_neg hs.le, div_eq_mul_inv]

private theorem balanced_low_power {A B z : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * (B / A) ^ z = A ^ (1 - z) * B ^ z := by
  rw [Real.div_rpow hB.le hA.le, Real.rpow_sub hA, Real.rpow_one]
  ring

private theorem balanced_high_power {A B z : ℝ} (hA : 0 < A) (hB : 0 < B) :
    B * (B / A) ^ (z - 1) = A ^ (1 - z) * B ^ z := by
  rw [Real.div_rpow hB.le hA.le, Real.rpow_sub hB, Real.rpow_sub hA,
    Real.rpow_sub hA, Real.rpow_one, Real.rpow_one]
  field_simp

/-- Balancing the threshold gives the product of the two weak moment bounds. -/
theorem lintegral_abs_rpow_le_interpolation {u : α → ℝ}
    (hu : AEMeasurable u μ) {l q p A B : ℝ}
    (hq : 0 < q) (hlq : l < q) (hqp : q < p)
    (hA : 0 < A) (hB : 0 < B)
    (hlow : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (A * s ^ (-l)))
    (hhigh : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (B * s ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) ≤
      ENNReal.ofReal ((1 / (1 - l / q) + 1 / (p / q - 1)) *
        A ^ ((p - q) / (p - l)) * B ^ ((q - l) / (p - l))) := by
  have hpl : p - l ≠ 0 := by linarith
  have hq₀ := hq.ne'
  have he₁ : q / (p - l) * (1 - l / q) = (q - l) / (p - l) := by
    field_simp
  have he₂ : q / (p - l) * (1 - p / q) = (q - l) / (p - l) - 1 := by
    field_simp
    ring
  have he₃ : 1 - (q - l) / (p - l) = (p - q) / (p - l) := by
    field_simp
    ring
  have h := lintegral_abs_rpow_le_of_tail_bounds hu hq hlq hqp hA.le hB.le
    (Real.rpow_pos_of_pos (div_pos hB hA) (q / (p - l))) hlow hhigh
  rw [← Real.rpow_mul (div_pos hB hA).le, he₁,
    ← Real.rpow_mul (div_pos hB hA).le, he₂] at h
  rw [balanced_low_power hA hB, balanced_high_power hA hB, he₃] at h
  have hd₁ : 0 < 1 - l / q := sub_pos.mpr ((div_lt_one hq).mpr hlq)
  have hd₂ : 0 < p / q - 1 := sub_pos.mpr ((one_lt_div hq).mpr hqp)
  have hn₁ : 0 ≤ A ^ ((p - q) / (p - l)) * B ^ ((q - l) / (p - l)) /
      (1 - l / q) := by positivity
  have hn₂ : 0 ≤ A ^ ((p - q) / (p - l)) * B ^ ((q - l) / (p - l)) /
      (p / q - 1) := by positivity
  rw [← ENNReal.ofReal_add hn₁ hn₂] at h
  convert h using 1
  congr 1
  ring

/-- A vanishing distribution bound forces every positive moment to vanish. -/
theorem lintegral_abs_rpow_eq_zero_of_tail_zero {u : α → ℝ}
    (hu : AEMeasurable u μ) {q : ℝ} (hq : 0 < q)
    (htail : ∀ s, 0 < s → μ {x | s < |u x|} = 0) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) = 0 := by
  have hm : AEMeasurable (fun x => |u x| ^ q) μ := by
    simpa only [Real.norm_eq_abs] using hu.norm.pow_const q
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hm]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hset : {x | t < |u x| ^ q} = {x | t ^ q⁻¹ < |u x|} := by
    ext x
    change t < |u x| ^ q ↔ t ^ q⁻¹ < |u x|
    conv_lhs => rw [← Real.rpow_inv_rpow ht.le hq.ne']
    exact Real.rpow_lt_rpow_iff (Real.rpow_nonneg ht.le _) (abs_nonneg _) hq
  change μ {x | t < |u x| ^ q} = 0
  rw [hset, htail _ (Real.rpow_pos_of_pos ht _)]

/-- Interpolation of nonnegative weak moment bounds, including the zero cases. -/
theorem lintegral_abs_rpow_le_interpolation_of_nonneg {u : α → ℝ}
    (hu : AEMeasurable u μ) {l q p A B : ℝ}
    (hq : 0 < q) (hlq : l < q) (hqp : q < p)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlow : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (A * s ^ (-l)))
    (hhigh : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (B * s ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) ≤
      ENNReal.ofReal ((1 / (1 - l / q) + 1 / (p / q - 1)) *
        A ^ ((p - q) / (p - l)) * B ^ ((q - l) / (p - l))) := by
  rcases hA.eq_or_lt with hA | hA
  · have ht : ∀ s, 0 < s → μ {x | s < |u x|} = 0 := by
      intro s hs
      simpa [← hA] using hlow s hs
    rw [lintegral_abs_rpow_eq_zero_of_tail_zero hu hq ht]
    exact bot_le
  rcases hB.eq_or_lt with hB | hB
  · have ht : ∀ s, 0 < s → μ {x | s < |u x|} = 0 := by
      intro s hs
      simpa [← hB] using hhigh s hs
    rw [lintegral_abs_rpow_eq_zero_of_tail_zero hu hq ht]
    exact bot_le
  exact lintegral_abs_rpow_le_interpolation hu hq hlq hqp hA hB hlow hhigh

/-- An L² function with a weak higher-power bound has a strong intermediate moment. -/
theorem lintegral_abs_rpow_le_of_memLp_two {u : α → ℝ}
    (hu : MemLp u 2 μ) {q p B : ℝ} (hq : 2 < q) (hqp : q < p) (hB : 0 ≤ B)
    (htail : ∀ s, 0 < s → μ {x | s < |u x|} ≤ ENNReal.ofReal (B * s ^ (-p))) :
    (∫⁻ x, ENNReal.ofReal (|u x| ^ q) ∂μ) ≤
      ENNReal.ofReal ((1 / (1 - 2 / q) + 1 / (p / q - 1)) *
        (∫ x, u x ^ 2 ∂μ) ^ ((p - q) / (p - 2)) * B ^ ((q - 2) / (p - 2))) := by
  have hi : Integrable (fun x => |u x| ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, sq_abs] using hu.integrable_sq
  have heq : (∫ x, |u x| ^ (2 : ℝ) ∂μ) = ∫ x, u x ^ 2 ∂μ := by
    simp only [Real.rpow_two, sq_abs]
  apply lintegral_abs_rpow_le_interpolation_of_nonneg hu.aemeasurable
    (by linarith) hq hqp (integral_nonneg (fun x => sq_nonneg _)) hB
    _ htail
  intro s hs
  simpa only [heq] using measure_abs_gt_le_integral_rpow (by norm_num : (0 : ℝ) < 2) hs hi

end HeatKernel.Sobolev
