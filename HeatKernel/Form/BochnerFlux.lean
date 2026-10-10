-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ProductL2
public import HeatKernel.Form.GradientCurves
public import HeatKernel.Moser.JointMeasurability
import Mathlib.Tactic.Linter

/-! # Bochner representatives of jointly square integrable fluxes -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace HeatKernel

/-- Product square integrability gives spatial square integrability at almost every parameter. -/
theorem ae_memLp_slice_of_product_memLp {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α → β → E}
    (hf : MemLp (Function.uncurry f) 2 (μ.prod ν)) :
    ∀ᵐ t ∂μ, MemLp (f t) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with t ht hi
  exact (memLp_two_iff_integrable_sq_norm ht).mpr hi

/-- Every jointly square integrable representative determines a Bochner L² curve. -/
theorem exists_L2_curve_of_product_memLp {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)] {f : α → β → E}
    (hf : MemLp (Function.uncurry f) 2 (μ.prod ν)) :
    ∃ F : α → Lp E 2 ν, MemLp F 2 μ ∧ ∀ᵐ t ∂μ, F t =ᵐ[ν] f t := by
  classical
  let F : α → Lp E 2 ν := fun t => if ht : MemLp (f t) 2 ν then ht.toLp (f t) else 0
  have hr : ∀ᵐ t ∂μ, F t =ᵐ[ν] f t := by
    filter_upwards [ae_memLp_slice_of_product_memLp hf] with t ht
    simpa only [F, dite_eq_left ht] using ht.coeFn_toLp
  exact ⟨F, memLp_L2_of_product_representatives hf hr, hr⟩

end HeatKernel
