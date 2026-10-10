-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerFluxCoordinates
public import HeatKernel.Moser.NegativePowerAffineFlux
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Spatial reciprocal-power absorption for the actual localized weak flux. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Each coordinate of the physical reciprocal-power flux is integrable from
bounded coefficients and cutoffs and the original square-integrable gradients. -/
theorem integrable_negative_power_coordinate_flux {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ}
    {c C K p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) (i : ι) :
    Integrable (fun x => (∑ j, a i j x * g j x) *
      (η x ^ 2 * (-p - 1) * (u x + c) ^ (-p - 2) * g i x +
        (2 * η x * d i x) * (u x + c) ^ (-p - 1))) μ := by
  have hprincipal := memLp_two_mul_of_ae_bound hη
    (memLp_two_mul_of_ae_bound hη
      (memLp_shifted_nonpositive_power_mul hc (by linarith : -p - 2 ≤ 0)
        hu hupos (hg i)) hηbound) hηbound
  have hmixed := memLp_two_mul_of_ae_bound hη
    (memLp_shifted_nonpositive_power_mul hc (by linarith : -p - 1 ≤ 0)
      hu hupos (hd i)) hηbound
  have hrow : MemLp (fun x => ∑ j, a i j x * g j x) 2 μ :=
    memLp_finsetSum _ fun j _ => memLp_two_mul_of_ae_bound (ha i j) (hg j) (hb i j)
  have htest := (hprincipal.const_mul (-p - 1)).add (hmixed.const_mul 2)
  have hprod := hrow.integrable_mul htest
  apply hprod.congr
  exact Filter.Eventually.of_forall fun x => by simp only [Pi.mul_def, Pi.add_def]; ring

end HeatKernel
