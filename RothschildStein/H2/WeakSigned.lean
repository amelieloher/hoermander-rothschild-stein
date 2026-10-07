-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorDistributionSplit

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Positive/negative splitting accounts for the factor two in
BB's weak-type constant (BB p. 320). -/
theorem operator_weak_signed_of_nonnegative (μ ν : Measure X) (hν : ν ≤ μ)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (E : Set X) (C : ℝ)
    (hweak : ∀ f : X → ℝ, ∀ hf : MemLp f 2 μ,
      (∀ᵐ x ∂μ, 0 ≤ f x) → (∀ᵐ x ∂μ, x ∉ E → f x = 0) →
      ∀ α : ℝ, 0 < α →
      distribution ν (fun x => (T ((hf.mono_measure hν).toLp f)) x) α ≤
        ENNReal.ofReal (C / α) * eLpNorm f 1 μ)
    (f : X → ℝ) (hf : MemLp f 2 μ)
    (hfs : ∀ᵐ x ∂μ, x ∉ E → f x = 0) {α : ℝ} (hα : 0 < α) :
    distribution ν (fun x => (T ((hf.mono_measure hν).toLp f)) x) α ≤
      ENNReal.ofReal (2 * C / α) * eLpNorm f 1 μ := by
  let fp : X → ℝ := fun x => max (f x) 0
  let fm : X → ℝ := fun x => max (-f x) 0
  have hp := hf.pos_part
  have hm := hf.neg_part
  have hsp : ∀ᵐ x ∂μ, x ∉ E → fp x = 0 := hfs.mono fun x hx h => by simp [fp, hx h]
  have hsm : ∀ᵐ x ∂μ, x ∉ E → fm x = 0 := hfs.mono fun x hx h => by simp [fm, hx h]
  have hwp := hweak fp hp (Eventually.of_forall fun x => le_max_right _ _) hsp (α / 2) (by positivity)
  have hwm := hweak fm hm (Eventually.of_forall fun x => le_max_right _ _) hsm (α / 2) (by positivity)
  have heq : (hf.mono_measure hν).toLp f =
      (hp.mono_measure hν).toLp fp - (hm.mono_measure hν).toLp fm := by
    apply Lp.ext
    filter_upwards [(hf.mono_measure hν).coeFn_toLp, (hp.mono_measure hν).coeFn_toLp,
      (hm.mono_measure hν).coeFn_toLp,
      Lp.coeFn_sub ((hp.mono_measure hν).toLp fp) ((hm.mono_measure hν).toLp fm)] with x hx hpx hmx hs
    rw [hx, hs]
    simp only [Pi.sub_apply]
    dsimp [fp, fm]
    rw [hpx, hmx]
    by_cases h : 0 ≤ f x
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
      ring
  have hsub : ∀ᵐ x ∂ν, |(T ((hf.mono_measure hν).toLp f)) x| ≤
      |(T ((hp.mono_measure hν).toLp fp)) x| + |(T ((hm.mono_measure hν).toLp fm)) x| := by
    rw [heq, T.map_sub]
    filter_upwards [Lp.coeFn_sub (T ((hp.mono_measure hν).toLp fp))
      (T ((hm.mono_measure hν).toLp fm))] with x hx
    rw [hx]
    simp only [Pi.sub_apply]
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      ((T ((hp.mono_measure hν).toLp fp)) x) (-((T ((hm.mono_measure hν).toLp fm)) x))
  have hnorm : eLpNorm fp 1 μ + eLpNorm fm 1 μ = eLpNorm f 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm hp.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
      ← lintegral_add_left' hp.aestronglyMeasurable.aemeasurable.enorm]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    congr 1
    dsimp [fp, fm]
    rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (le_max_right _ _)]
    by_cases h : 0 ≤ f x
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith), abs_of_neg (lt_of_not_ge h), zero_add]
  calc
    _ ≤ distribution ν (fun x => (T ((hp.mono_measure hν).toLp fp)) x) (α / 2) +
        distribution ν (fun x => (T ((hm.mono_measure hν).toLp fm)) x) (α / 2) := distribution_add_le ν hsub α
    _ ≤ ENNReal.ofReal (C / (α / 2)) * (eLpNorm fp 1 μ + eLpNorm fm 1 μ) :=
      (add_le_add hwp hwm).trans_eq (mul_add _ _ _).symm
    _ = _ := by rw [hnorm]; congr 2; field_simp

end RothschildStein.H2
