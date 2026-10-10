-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderCutoffIntegrability
public import HeatKernel.Form.Ellipticity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Finite small-power moments and spatial cutoff comparisons. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace HeatKernel

/-- Local square integrability on a finite measure space gives every shifted
small positive moment without an upper bound on the value. -/
theorem integrable_shifted_small_power_of_memLp_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {c p : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : MemLp u 2 μ) (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x) :
    Integrable (fun x => (u x + c) ^ p) μ := by
  have hdom : Integrable (fun x => (2 + c) + u x ^ 2) μ :=
    (integrable_const (2 + c)).add hu.integrable_sq
  apply hdom.mono'
    (((hu.aestronglyMeasurable.add aestronglyMeasurable_const).aemeasurable.pow_const p).aestronglyMeasurable)
  filter_upwards [hu0] with x hx
  have hs : 0 < u x + c := add_pos_of_nonneg_of_pos hx hc
  have hpower : (u x + c) ^ p ≤ 1 + (u x + c) := by
    by_cases hs1 : 1 ≤ u x + c
    · exact (Real.rpow_le_self_of_one_le hs1 hp1).trans (by linarith)
    · exact (Real.rpow_le_one hs.le (le_of_not_ge hs1) hp).trans (by linarith)
  change ‖(u x + c) ^ p‖ ≤ (2 + c) + u x ^ 2
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hs.le p)]
  nlinarith only [hpower, sq_nonneg (u x - 1 / 2)]

/-- A bounded nonnegative weight supported in a measurable set is integrable
against its finite moment there, and costs at most its uniform weight bound. -/
theorem integrable_supported_weighted_moment_and_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {V : Set α} (hV : MeasurableSet V) {f w : α → ℝ} {C : ℝ}
    (hf : IntegrableOn f V μ) (hf0 : ∀ᵐ x ∂μ.restrict V, 0 ≤ f x)
    (hw : AEStronglyMeasurable w μ) (hw0 : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hwC : ∀ᵐ x ∂μ, w x ≤ C) (hs : ∀ x ∉ V, w x = 0) :
    Integrable (fun x => w x * f x) μ ∧
      0 ≤ (∫ x, w x * f x ∂μ) ∧ (∫ x, w x * f x ∂μ) ≤ C * ∫ x in V, f x ∂μ := by
  have hfi := hf.integrable_indicator hV
  have hwbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C := by
    filter_upwards [hw0, hwC] with x hx hC
    simpa only [Real.norm_of_nonneg hx] using hC
  have hi : Integrable (fun x => w x * f x) μ := by
    apply (hfi.mul_bdd hw hwbound).congr
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ V
    · simp only [indicator_of_mem hx, mul_comm]
    · simp only [indicator_of_notMem hx, hs x hx, zero_mul]
  have hf0' := (ae_restrict_iff' hV).mp hf0
  have hpositive : ∀ᵐ x ∂μ, 0 ≤ w x * f x := by
    filter_upwards [hf0', hw0] with x hx hwx
    by_cases hmem : x ∈ V
    · exact mul_nonneg hwx (hx hmem)
    · simp only [hs x hmem, zero_mul, le_refl]
  refine ⟨hi, integral_nonneg_of_ae hpositive, ?_⟩
  have hbound := integral_mono_ae hi (hfi.const_mul C) (by
    filter_upwards [hf0', hwC] with x hx hwx
    by_cases hmem : x ∈ V
    · simpa only [indicator_of_mem hmem] using mul_le_mul_of_nonneg_right hwx (hx hmem)
    · simp only [hs x hmem, indicator_of_notMem hmem, zero_mul, mul_zero, le_refl])
  simpa only [integral_const_mul, integral_indicator hV] using hbound

/-- Unit spatial cutoffs and their squared gradient bound control the literal
small-power value and cutoff-gradient moments on the outer region. -/
theorem reverse_holder_cutoff_moment_bounds {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {V : Set α} (hV : MeasurableSet V) {f η : α → ℝ} {d : ι → α → ℝ} {L : ℝ}
    (hf : IntegrableOn f V μ) (hf0 : ∀ᵐ x ∂μ.restrict V, 0 ≤ f x)
    (hη : AEStronglyMeasurable η μ) (hηunit : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hηsupport : ∀ x ∉ V, η x = 0) (hd : ∀ i, MemLp (d i) 2 μ)
    (hdsupport : ∀ i x, x ∉ V → d i x = 0)
    (hdL : ∀ᵐ x ∂μ, coordinateNormSq (fun i => d i x) ≤ L) :
    Integrable (fun x => η x ^ 2 * f x) μ ∧
      Integrable (fun x => f x * coordinateNormSq (fun i => d i x)) μ ∧
      0 ≤ (∫ x, η x ^ 2 * f x ∂μ) ∧
      (∫ x, η x ^ 2 * f x ∂μ) ≤ ∫ x in V, f x ∂μ ∧
      (∫ x, f x * coordinateNormSq (fun i => d i x) ∂μ) ≤ L * ∫ x in V, f x ∂μ := by
  have hηbound : ∀ᵐ x ∂μ, η x ^ 2 ≤ 1 := Filter.Eventually.of_forall fun x => by
    obtain ⟨h0, h1⟩ := hηunit x
    nlinarith only [h0, h1]
  obtain ⟨hηi, hη0, hηle⟩ := integrable_supported_weighted_moment_and_bound hV hf hf0
    (hη.pow 2) (Filter.Eventually.of_forall fun x => sq_nonneg _) hηbound
    (fun x hx => by simp only [Pi.pow_apply, hηsupport x hx, zero_pow (by decide : 2 ≠ 0)])
  have hdi : Integrable (fun x => coordinateNormSq (fun i => d i x)) μ := by
    unfold coordinateNormSq
    exact integrable_finsetSum _ fun i _ => (hd i).integrable_sq
  have hd0 (x : α) : 0 ≤ coordinateNormSq (fun i => d i x) := by
    unfold coordinateNormSq
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hdf, _, hdle⟩ := integrable_supported_weighted_moment_and_bound hV hf hf0
    hdi.aestronglyMeasurable (Filter.Eventually.of_forall hd0) hdL (by
      intro x hx
      unfold coordinateNormSq
      exact Finset.sum_eq_zero fun i _ => by
        change d i x ^ 2 = 0
        rw [hdsupport i x hx]
        norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Pi.pow_apply] using hηi
  · simpa only [mul_comm] using hdf
  · simpa only [Pi.pow_apply] using hη0
  · simpa only [Pi.pow_apply, one_mul] using hηle
  · simpa only [mul_comm] using hdle

end HeatKernel
