-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicMatrixAbsorption
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Cutoff-energy bounds for logarithmic matrix absorption -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A cutoff gradient supported in a finite-measure set has total matrix energy
bounded by that set's volume, even when the ambient measure is infinite. -/
theorem integral_logarithmic_cutoff_energy_le_of_support {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {d : ι → α → ℝ} {C upper L : ℝ} {S : Set α}
    (hS : MeasurableSet S) (hfinite : μ S ≠ ⊤)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hd : ∀ i, MemLp (d i) 2 μ) (hupper : 0 ≤ upper)
    (hquad : ∀ᵐ x ∂μ, ∀ ξ, matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ)
    (hgrad : ∀ᵐ x ∂μ, x ∈ S → coordinateNormSq (fun i => d i x) ≤ L)
    (hsupport : ∀ᵐ x ∂μ, x ∉ S → ∀ i, d i x = 0) :
    (∫ x, matrixEnergy (fun i j => a i j x) (fun i => d i x) ∂μ) ≤
      upper * L * μ.real S := by
  have hi : Integrable (fun x => matrixEnergy (fun i j => a i j x) (fun i => d i x)) μ :=
    integrable_matrix_pairing ha hb hd hd
  have hmajor : Integrable (S.indicator (fun _ => upper * L)) μ :=
    (integrableOn_const (C := upper * L) hfinite).integrable_indicator hS
  have hm := integral_mono_ae hi hmajor (by
    filter_upwards [hquad, hgrad, hsupport] with x hx hg hs
    by_cases hmem : x ∈ S
    · rw [Set.indicator_of_mem hmem]
      exact (hx (fun i => d i x)).trans (mul_le_mul_of_nonneg_left (hg hmem) hupper)
    · rw [Set.indicator_of_notMem hmem]
      simp only [matrixEnergy, hs hmem, mul_zero, Finset.sum_const_zero, le_refl])
  simpa only [integral_indicator_const (upper * L) hS, smul_eq_mul, mul_comm] using hm

end HeatKernel
