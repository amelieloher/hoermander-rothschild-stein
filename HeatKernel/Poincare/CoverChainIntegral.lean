-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.ChainEnergyBound
public import HeatKernel.Poincare.OverlapIntegral

/-! Summing local oscillations using chains, shadows, and energy overlap. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- A countable cover's local chain estimates yield a global energy estimate.
The radius, shadow, and overlap bounds are explicit geometric inputs. -/
theorem setLIntegral_le_energy_of_cover_chain_bounds {E ι κ : Type*}
    [MeasurableSpace E] [Countable ι] [Countable κ]
    (μ : Measure E) (U : Set E) (A : ι → Set E) (D : κ → Set E)
    (hcover : U ⊆ ⋃ i, A i) (hD : ∀ j, MeasurableSet (D j)) (hDU : ∀ j, D j ⊆ U)
    (f g : E → ℝ≥0∞) (hg : AEMeasurable g (μ.restrict U))
    (chain : ι → Finset κ) (m : ι → ℝ≥0∞) (v : κ → ℝ≥0∞)
    (w h : κ → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) (R r : ℝ≥0) (H C : ℝ≥0∞) (M : ℕ)
    (hlocal : ∀ i, (∫⁻ x in A i, f x ∂μ) ≤
      C * (m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)))
    (hradius : ∀ i, ∑ j ∈ chain i, w j ≤ R) (hmax : ∀ j, w j ≤ r)
    (hshadow : ∀ j, (∑' i : {i | j ∈ chain i}, m i.val) ≤ H * v j)
    (henergy : ∀ j, v j * ((h j ^ p : ℝ≥0) : ℝ≥0∞) ≤ ∫⁻ x in D j, g x ∂μ)
    (hfinite : ∀ x, {j | x ∈ D j}.Finite)
    (hcard : ∀ x, {j | x ∈ D j}.ncard ≤ M) :
    (∫⁻ x in U, f x ∂μ) ≤
      C * ((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * r * M * ∫⁻ x in U, g x ∂μ := by
  have hover := tsum_setLIntegral_le_mul_lintegral_of_overlap
    (μ.restrict U) D hD g hg M hfinite hcard
  simp_rw [Measure.restrict_restrict_of_subset (hDU _)] at hover
  have hchain := tsum_mul_chain_rpow_le_energy_sum chain m v
    (fun j => ∫⁻ x in D j, g x ∂μ) w h hp R r H hradius hmax hshadow henergy
  calc
    (∫⁻ x in U, f x ∂μ) ≤ ∫⁻ x in ⋃ i, A i, f x ∂μ :=
      lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
    _ ≤ ∑' i, ∫⁻ x in A i, f x ∂μ := lintegral_iUnion_le A f
    _ ≤ ∑' i, C * (m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞)) :=
      ENNReal.tsum_le_tsum hlocal
    _ = C * ∑' i, m i * (((∑ j ∈ chain i, w j * h j) ^ p : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.tsum_mul_left
    _ ≤ C * (((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * r *
        ∑' j, ∫⁻ x in D j, g x ∂μ) := mul_le_mul_right hchain C
    _ ≤ C * (((R ^ (p - 1) : ℝ≥0) : ℝ≥0∞) * H * r *
        (M * ∫⁻ x in U, g x ∂μ)) :=
      mul_le_mul_right (mul_le_mul_right hover _) C
    _ = _ := by ac_rfl

end HeatKernel
