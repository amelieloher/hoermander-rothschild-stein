-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FarKernelTransfer
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.H3

/-- far part. The actual absolute source mass is bounded by
 the volume of its support domain times its global L-infinity norm.
Measurability, integrability and zero extension are proved for the compact
continuous input (BB Proposition 8.53, p. 383). -/
theorem integral_abs_le_support_volume_mul_lpNorm_top {N : ℕ}
    {u : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    {A : Set (Fin N → ℝ)} (hA : MeasurableSet A) (hAfin : volume A < ∞)
    (hs : tsupport u ⊆ A) :
    (∫ y, |u y|) ≤ (volume A).toReal * lpNorm u ∞ volume := by
  let finiteA : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.mpr hAfin.ne
  let U := lpNorm u ∞ volume
  have huTop : MemLp u ∞ volume := hu.memLp_of_hasCompactSupport hsu
  have huabs : Integrable (fun y => |u y|) volume := hu.abs.integrable_of_hasCompactSupport hsu.abs
  have he : (fun y => |u y|) = A.indicator (fun y => |u y|) := by
    funext y
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)), abs_zero]
  have hc : Integrable (fun _ : Fin N → ℝ => U) (volume.restrict A) := integrable_const U
  have hb : ∀ᵐ y ∂volume.restrict A, |u y| ≤ U := ae_restrict_of_ae (by
    simpa only [Real.norm_eq_abs] using ae_le_lpNorm_exponent_top huTop)
  calc
    (∫ y, |u y|) = ∫ y in A, |u y| := by rw [← integral_indicator hA, ← he]
    _ ≤ ∫ _y in A, U := integral_mono_ae (huabs.mono_measure Measure.restrict_le_self) hc hb
    _ = _ := by rw [integral_const]; simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, U]

end RothschildStein.H3
