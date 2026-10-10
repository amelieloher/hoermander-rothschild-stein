-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! # Time integrals in endpoint mean-value estimates

A uniform slice bound integrates over the endpoint cylinder with its exact time
length. Applying the mean-value factor once and twice gives the constants four
and sixteen. The optimized exponential is computed at the heat radius.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
namespace HeatKernel.Gaussian

/-- A uniform bound integrates over the endpoint cylinder with time length
exactly four times the squared spatial radius. -/
theorem integral_endpoint_cylinder_le {f : ℝ → ℝ} {s r E : ℝ}
    (hf : IntegrableOn f (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)))
    (hbound : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ ≤ E) :
    (∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ) ≤ 4 * r ^ 2 * E := by
  have hlen : (s + r ^ 2 / 2) - (s - 7 * r ^ 2 / 2) = 4 * r ^ 2 := by ring
  calc
    _ ≤ ∫ _σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), E := by
      apply integral_mono_ae hf (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
      exact ae_restrict_of_forall_mem measurableSet_Ioo hbound
    _ = 4 * r ^ 2 * E := by
      rw [setIntegral_const, measureReal_def, Real.volume_Ioo, hlen, ENNReal.toReal_ofReal (by positivity)]
      rfl

/-- One endpoint mean-value estimate and a uniform slice bound give the
single-volume row factor. -/
theorem sq_le_of_endpoint_mean_value {f : ℝ → ℝ} {s r C V E p : ℝ}
    (hr : 0 < r) (hV : 0 < V)
    (hf : IntegrableOn f (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)))
    (hbound : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ ≤ E)
    (hmean : p ^ 2 ≤ C ^ 2 / (r ^ 2 * V) *
      ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ) :
    p ^ 2 ≤ 4 * C ^ 2 / V * E := by
  calc
    p ^ 2 ≤ _ := hmean
    _ ≤ C ^ 2 / (r ^ 2 * V) * (4 * r ^ 2 * E) :=
      mul_le_mul_of_nonneg_left (integral_endpoint_cylinder_le hf hbound) (by positivity)
    _ = _ := by field_simp

/-- Two endpoint mean-value estimates give the exact product-volume constant. -/
theorem sq_le_of_two_endpoint_mean_values {f : ℝ → ℝ} {s r C V W E p : ℝ}
    (hr : 0 < r) (hV : 0 < V) (hW : 0 < W)
    (hf : IntegrableOn f (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)))
    (hbound : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ ≤ 4 * C ^ 2 / W * E)
    (hmean : p ^ 2 ≤ C ^ 2 / (r ^ 2 * V) *
      ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), f σ) :
    p ^ 2 ≤ 16 * C ^ 4 / (V * W) * E := by
  have H := sq_le_of_endpoint_mean_value hr hV hf hbound hmean
  convert H using 1
  field_simp
  ring

/-- At the heat radius and optimized weight, the exponent has its normalized
quadratic and linear form. -/
theorem endpoint_weight_exponent_eq {t : ℝ} (ht : 0 < t) (ρ : ℝ) :
    let r := Real.sqrt t / 4;
    let β := ρ / (6 * t);
    (-2 * β * ρ + 8 * β * r + 6 * β ^ 2 * t) =
      -(ρ / Real.sqrt t) ^ 2 / 6 + (ρ / Real.sqrt t) / 3 := by
  dsimp
  have hs := Real.sq_sqrt ht.le
  have hu := Real.sqrt_pos.mpr ht
  generalize Real.sqrt t = u at *
  rw [← hs]
  field_simp [hu.ne']
  ring

end HeatKernel.Gaussian
