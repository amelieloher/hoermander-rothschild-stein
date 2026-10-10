-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderSpatialEnergyBound
public import HeatKernel.Moser.NegativePowerFluxCoordinates
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Concave-power physical flux controlled by horizontal coordinate energy. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Square-integrable original gradients control the physical concave-power
flux and its cutoff error, with the sign required by the time-energy balance. -/
theorem integrable_reverse_holder_physical_flux_and_bound {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ}
    {c C K ell upper p : ℝ} (hc : 0 < c) (hell : 0 < ell) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hcut : ∀ i, MemLp (fun x => (u x + c) ^ (p / 2) * d i x) 2 μ)
    (hcoeff : ∀ᵐ x ∂μ, (∀ i j, a i j x = a j i x) ∧ ∀ ξ : ι → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ) :
    let D := fun x => 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u x + c) ^ (p / 2 - 1) * g i x))
    let F := fun x => ∑ i, (∑ j, a i j x * g j x) *
      (η x ^ 2 * (p - 1) * (u x + c) ^ (p - 2) * g i x +
        (2 * η x * d i x) * (u x + c) ^ (p - 1))
    let R := fun x => 2 * upper * (u x + c) ^ p *
      coordinateNormSq (fun i => d i x)
    Integrable D μ ∧ Integrable F μ ∧ Integrable R μ ∧
      (∫ x, D x ∂μ) ≤ -p * (∫ x, F x ∂μ) + ∫ x, R x ∂μ := by
  dsimp only
  obtain ⟨hD, hF, hR, hbound⟩ := integrable_reverse_holder_spatial_energy_and_bound
    hc hell hp hp2 hu hupos hη hηbound ha hb hg hcut hcoeff
  have hflux := hupos.mono fun x hx => negative_power_weighted_flux_eq
    (fun i j => a i j x) (fun i => g i x) (fun i => d i x)
    (by linarith : 0 < u x + c) (-p) (η x)
  have hcut := hupos.mono fun x hx => negative_power_weighted_coordinate_norm_sq
    (fun i => d i x) (by linarith : 0 < u x + c) (-p)
  simp only [neg_neg] at hflux hcut
  have hcoef : -p + 1 = 1 - p := by ring
  rw [hcoef] at hflux
  have hFeq := hflux
  have hReq : (fun x => 2 * upper * coordinateNormSq
      (fun i => (u x + c) ^ (p / 2) * d i x)) =ᵐ[μ]
      (fun x => 2 * upper * (u x + c) ^ p * coordinateNormSq (fun i => d i x)) := by
    filter_upwards [hcut] with x hx
    rw [hx]
    ring
  have hphysical := hF.congr hFeq |>.neg
  refine ⟨hD, ?_, hR.congr hReq, ?_⟩
  · exact hphysical.congr (Filter.Eventually.of_forall fun x => neg_neg _)
  · rw [integral_congr_ae hFeq, integral_congr_ae hReq, integral_neg] at hbound
    simpa only [mul_neg, neg_mul] using hbound

end HeatKernel
