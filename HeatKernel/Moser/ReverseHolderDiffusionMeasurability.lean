-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.Ellipticity
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Time measurability of literal small-positive-power diffusion. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Jointly measurable localized representatives give the measurable diffusion
integral required by backward absorption, without assuming its integrability. -/
theorem aestronglyMeasurable_reverse_holder_diffusion {T α ι : Type*}
    [MeasurableSpace T] [MeasurableSpace α] [Fintype ι]
    {τ : Measure T} {μ : Measure α} [SFinite μ]
    {u : T × α → ℝ} {g : ι → T × α → ℝ} {η : α → ℝ} (c p ell : ℝ)
    (hu : AEStronglyMeasurable u (τ.prod μ))
    (hg : ∀ i, AEStronglyMeasurable (g i) (τ.prod μ))
    (hη : AEStronglyMeasurable η μ) :
    AEStronglyMeasurable (fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u (t, x) + c) ^ (p / 2 - 1) * g i (t, x))) ∂μ) τ := by
  have hd (i : ι) : AEStronglyMeasurable
      (fun z : T × α => η z.2 * ((u z + c) ^ (p / 2 - 1) * g i z)) (τ.prod μ) :=
    hη.comp_snd.fun_mul
      (((hu.fun_add aestronglyMeasurable_const).aemeasurable.pow_const _).aestronglyMeasurable.fun_mul
        (hg i))
  have hs : AEStronglyMeasurable (fun z : T × α => coordinateNormSq
      (fun i => η z.2 * ((u z + c) ^ (p / 2 - 1) * g i z))) (τ.prod μ) := by
    unfold coordinateNormSq
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hd i).pow 2)
  exact (hs.const_mul (2 * ell * (p / 2) ^ 2)).integral_prod_right'

end HeatKernel
