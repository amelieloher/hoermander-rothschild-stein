-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TailIntegrals
public import RothschildStein.H2.FiniteMomentSupport

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- Subadditivity splits a distribution function at half the level,
with an a.e. subadditivity hypothesis (BB Thm 7.48, p. 334). -/
theorem distribution_add_le (μout : Measure Z) {F G H : Z → ℝ}
    (hsub : ∀ᵐ z ∂μout, |F z| ≤ |G z| + |H z|) (t : ℝ) :
    distribution μout F t ≤ distribution μout G (t / 2) + distribution μout H (t / 2) := by
  apply (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hsub] with z hz
  intro ht
  change t < |F z| at ht
  change t / 2 < |G z| ∨ t / 2 < |H z|
  by_contra hh
  push Not at hh
  linarith

private theorem weight_first {t p c : ℝ} (ht : 0 < t) :
    t ^ (p - 1) * (c / (t / 2)) = (2 * c) * t ^ (p - 2) := by
  rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub ht (p - 1) 1, Real.rpow_one]
  field_simp

private theorem weight_second {t p q c : ℝ} (ht : 0 < t) :
    t ^ (p - 1) * (c / ((t / 2) ^ q)) = (2 ^ q * c) * t ^ (p - 1 - q) := by
  rw [Real.div_rpow ht.le (by positivity : (0 : ℝ) ≤ 2), Real.rpow_sub ht (p - 1) q]
  have htq := (Real.rpow_pos_of_pos ht q).ne'
  have htwo := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) q).ne'
  field_simp

/-- Integrating the exact finite-endpoint split distribution estimate
(BB Thm 7.48, p. 334). No input measure finiteness is required. -/
theorem moment_bound_of_finite_split
    (ν : Measure Y) (μout : Measure Z) {f : Y → ℝ} {F : Z → ℝ}
    (hfmeas : Measurable f) (hF : AEMeasurable F μout)
    {c₁ c₂ p q : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hp : 1 < p) (hpq : p < q)
    (hfin : moment ν p f < ∞)
    (hdist : ∀ {t : ℝ}, 0 < t → distribution μout F t ≤
      ENNReal.ofReal (c₁ / (t / 2)) * moment ν 1 (highPart f t) +
      ENNReal.ofReal (c₂ / ((t / 2) ^ q)) * moment ν q (lowPart f t)) :
    moment μout p F ≤
      ENNReal.ofReal (p * (2 * c₁ / (p - 1) + 2 ^ q * c₂ / (q - p))) * moment ν p f := by
  let μ := ν.restrict {y | f y ≠ 0}
  let : SFinite μ := sFinite_restrict_of_moment_lt_top ν hfmeas (by linarith) hfin
  have hm : moment μ p f = moment ν p f := moment_restrict_support ν (by simp) (by linarith)
  have hh (t : ℝ) : moment μ 1 (highPart f t) = moment ν 1 (highPart f t) :=
    moment_restrict_support ν (by intro y hy; simp [highPart, not_ne_iff.mp hy]) zero_lt_one
  have hl (t : ℝ) : moment μ q (lowPart f t) = moment ν q (lowPart f t) :=
    moment_restrict_support ν (by intro y hy; simp [lowPart, not_ne_iff.mp hy]) (by linarith)
  have hdistμ := fun {t : ℝ} (ht : 0 < t) => show distribution μout F t ≤
      ENNReal.ofReal (c₁ / (t / 2)) * moment μ 1 (highPart f t) +
      ENNReal.ofReal (c₂ / ((t / 2) ^ q)) * moment μ q (lowPart f t) from
    (by rw [hh, hl]; exact hdist ht)
  rw [← hm]
  rw [layerCake μout hF (by linarith)]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (2 * c₁) *
          (ENNReal.ofReal (t ^ (p - 2)) * moment μ 1 (highPart f t)) +
        ENNReal.ofReal (2 ^ q * c₂) *
          (ENNReal.ofReal (t ^ (p - 1 - q)) * moment μ q (lowPart f t)) := by
      apply mul_le_mul' le_rfl (lintegral_mono_ae ?_)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      have hd := mul_le_mul' (hdistμ ht) (le_refl (ENNReal.ofReal (t ^ (p - 1))))
      rw [add_mul] at hd
      have he₁ : ENNReal.ofReal (c₁ / (t / 2)) * moment μ 1 (highPart f t) *
          ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal (2 * c₁) *
            (ENNReal.ofReal (t ^ (p - 2)) * moment μ 1 (highPart f t)) := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity),
          mul_comm (c₁ / (t / 2)) _, weight_first ht,
          ENNReal.ofReal_mul (by positivity), mul_assoc]
      have he₂ : ENNReal.ofReal (c₂ / ((t / 2) ^ q)) * moment μ q (lowPart f t) *
          ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal (2 ^ q * c₂) *
            (ENNReal.ofReal (t ^ (p - 1 - q)) * moment μ q (lowPart f t)) := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity),
          mul_comm (c₂ / ((t / 2) ^ q)) _, weight_second ht,
          ENNReal.ofReal_mul (by positivity), mul_assoc]
      rwa [he₁, he₂] at hd
    _ = _ := by
      have hmh := measurable_moment_highPart μ hfmeas 1
      rw [lintegral_add_left (by fun_prop),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        highPart_tail_integral μ hfmeas hp,
        lowPart_tail_integral μ hfmeas (by linarith) hpq]
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← add_mul,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2; ring

end RothschildStein.H2
