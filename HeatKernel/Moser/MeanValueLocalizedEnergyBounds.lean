-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! # Slice and integrated energy from a primitive dissipation budget -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- A primitive budget controls the localized value energy after dropping its
nonnegative accumulated dissipation. All primitive and dissipation comparisons
are explicit inputs. -/
theorem ae_localized_value_energy_le_of_primitive_budget
    {a b p H L : ℝ} (hp : 0 < p)
    {χ E D f m : ℝ → ℝ}
    (hχ0 : ∀ t ∈ Icc a b, 0 ≤ χ t) (hD0 : ∀ t, 0 ≤ D t)
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), f t ≤ p * E t)
    (hbudget : ∀ᵐ t ∂volume.restrict (Icc a b),
      χ t * E t + (∫ s in Icc a t, χ s * D s) ≤
        (H / p + 2 * L) * (∫ s in Icc a b, m s)) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      χ t * f t ≤ (H + 2 * p * L) * (∫ s in Icc a b, m s) := by
  filter_upwards [hf, hbudget, self_mem_ae_restrict measurableSet_Icc] with t hft ht htm
  have hacc : 0 ≤ ∫ s in Icc a t, χ s * D s := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    exact mul_nonneg (hχ0 s ⟨hs.1, hs.2.trans htm.2⟩) (hD0 s)
  have hs := mul_le_mul_of_nonneg_left hft (hχ0 t htm)
  have hb := mul_le_mul_of_nonneg_left ht hp.le
  have heq : p * ((H / p + 2 * L) * (∫ s in Icc a b, m s)) =
      (H + 2 * p * L) * (∫ s in Icc a b, m s) := by
    field_simp
  rw [heq] at hb
  nlinarith only [hs, hb, mul_nonneg hp.le hacc]

/-- The complete cutoff product gradient and a total dissipation budget give
the full integrated Sobolev energy. Integrability and the two spatial quadratic
comparisons are explicit inputs. -/
theorem integral_localized_sobolev_energy_le_of_dissipation_budget
    {a b p H L : ℝ} (hp : 0 < p) (hL : 0 ≤ L)
    {χ D f g m : ℝ → ℝ} (hχ : Continuous χ)
    (hχunit : ∀ t ∈ Icc a b, χ t ∈ Icc (0 : ℝ) 1)
    (hD : IntegrableOn D (Icc a b)) (hm : IntegrableOn m (Icc a b))
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hi : IntegrableOn (fun t => χ t * (g t + f t)) (Icc a b))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), f t ≤ m t)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), g t ≤ 2 * p * D t + 2 * L * m t)
    (hbudget : (∫ t in Icc a b, χ t * D t) ≤
      (H / p + 2 * L) * (∫ t in Icc a b, m t)) :
    (∫ t in Icc a b, χ t * (g t + f t)) ≤
      (2 * H + (4 * p + 2) * L + 1) * (∫ t in Icc a b, m t) := by
  have hχD : IntegrableOn (fun t => χ t * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuousOn hD isCompact_Icc
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc a b),
      χ t * (g t + f t) ≤ 2 * p * (χ t * D t) + (2 * L + 1) * m t := by
    filter_upwards [hf, hg, hm0, self_mem_ae_restrict measurableSet_Icc]
      with t hft hgt hmt ht
    have hgχ := mul_le_mul_of_nonneg_left hgt (hχunit t ht).1
    have hfχ := mul_le_mul_of_nonneg_left hft (hχunit t ht).1
    have hχm := mul_le_mul_of_nonneg_right (hχunit t ht).2 hmt
    have hLχm := mul_le_mul_of_nonneg_left hχm hL
    nlinarith only [hgχ, hfχ, hχm, hLχm]
  have hb := integral_mono_ae hi
    ((hχD.const_mul (2 * p)).add (hm.const_mul (2 * L + 1))) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add (hχD.const_mul (2 * p)) (hm.const_mul (2 * L + 1)),
    integral_const_mul, integral_const_mul] at hb
  have ht := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 * p by positivity)
  have heq : 2 * p * ((H / p + 2 * L) * (∫ t in Icc a b, m t)) +
      (2 * L + 1) * (∫ t in Icc a b, m t) =
        (2 * H + (4 * p + 2) * L + 1) * (∫ t in Icc a b, m t) := by
    field_simp
    ring
  exact hb.trans (by linarith only [ht, heq])

/-- Squaring a smooth unit temporal cutoff doubles its upper derivative bound. -/
theorem deriv_sq_cutoff_le {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    {t T : ℝ} (ht : θ t ∈ Icc (0 : ℝ) 1) (hT : 0 ≤ T) (hd : deriv θ t ≤ T) :
    deriv (fun s => θ s ^ 2) t ≤ 2 * T := by
  have he := deriv_pow (hθ.differentiable (by simp) t) 2
  change deriv (fun s => θ s ^ 2) t = _ at he
  rw [he]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have h1 := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht.1)
  have h2 := mul_le_mul_of_nonneg_right ht.2 hT
  nlinarith only [h1, h2]

end HeatKernel
