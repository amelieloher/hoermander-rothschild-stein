-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Almost-everywhere order bounds in L² limits -/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem ae_nonneg_of_tendsto_L2 {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (hlim : Tendsto f atTop (𝓝 g)) (hf : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) :
    ∀ᵐ x ∂μ, 0 ≤ g x := by
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
  exact ge_of_tendsto' hφx (fun n => Set.mem_iInter.mp hx (φ n))

theorem ae_le_const_of_tendsto_L2 {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} {c : ℝ}
    (hlim : Tendsto f atTop (𝓝 g)) (hf : ∀ n, ∀ᵐ x ∂μ, f n x ≤ c) :
    ∀ᵐ x ∂μ, g x ≤ c := by
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
  exact le_of_tendsto' hφx (fun n => Set.mem_iInter.mp hx (φ n))

end HeatKernel
