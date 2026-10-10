-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerSpatialEnergyBound
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Coordinate identities for reciprocal-power diffusion and cutoff flux. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- The two reciprocal half-power weights recover the full diffusion weight. -/
theorem negative_power_weighted_matrix_energy {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (g : ι → ℝ) {s : ℝ} (hs : 0 < s) (p η : ℝ) :
    matrixEnergy a (fun i => η * (s ^ (-p / 2 - 1) * g i)) =
      η ^ 2 * s ^ (-p - 2) * matrixEnergy a g := by
  have hpow : s ^ (-p / 2 - 1) * s ^ (-p / 2 - 1) = s ^ (-p - 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  simp only [matrixEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = η ^ 2 * (s ^ (-p / 2 - 1) * s ^ (-p / 2 - 1)) *
        (a i j * g j * g i) := by ring
    _ = _ := by rw [hpow]

/-- The mixed half-power weights recover the reciprocal-power cutoff flux. -/
theorem negative_power_weighted_matrix_pairing {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (g d : ι → ℝ) {s : ℝ} (hs : 0 < s) (p η : ℝ) :
    (∑ i, ∑ j, a i j * (η * (s ^ (-p / 2 - 1) * g j)) *
      (s ^ (-p / 2) * d i)) =
      η * s ^ (-p - 1) * (∑ i, ∑ j, a i j * g j * d i) := by
  have hpow : s ^ (-p / 2 - 1) * s ^ (-p / 2) = s ^ (-p - 1) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = η * (s ^ (-p / 2 - 1) * s ^ (-p / 2)) * (a i j * g j * d i) := by ring
    _ = _ := by rw [hpow]

/-- Squaring the reciprocal half-power cutoff gradient gives its full weight. -/
theorem negative_power_weighted_coordinate_norm_sq {ι : Type*} [Fintype ι]
    (d : ι → ℝ) {s : ℝ} (hs : 0 < s) (p : ℝ) :
    coordinateNormSq (fun i => s ^ (-p / 2) * d i) =
      s ^ (-p) * coordinateNormSq d := by
  have hpow : (s ^ (-p / 2)) ^ 2 = s ^ (-p) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [coordinateNormSq, mul_pow, hpow, Finset.mul_sum]

/-- The weighted quadratic form is exactly the negative of the physical
reciprocal-power test flux, including its cutoff-gradient contribution. -/
theorem negative_power_weighted_flux_eq {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (g d : ι → ℝ) {s : ℝ} (hs : 0 < s) (p η : ℝ) :
    (p + 1) * matrixEnergy a (fun i => η * (s ^ (-p / 2 - 1) * g i)) -
      2 * (∑ i, ∑ j, a i j * (η * (s ^ (-p / 2 - 1) * g j)) *
        (s ^ (-p / 2) * d i)) =
      -(∑ i, (∑ j, a i j * g j) *
        (η ^ 2 * (-p - 1) * s ^ (-p - 2) * g i +
          (2 * η * d i) * s ^ (-p - 1))) := by
  rw [negative_power_weighted_matrix_energy a g hs,
    negative_power_weighted_matrix_pairing a g d hs]
  simp only [matrixEnergy, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Square-integrable original gradients control the physical reciprocal-power
flux and its cutoff error, with the sign required by the time-energy balance. -/
theorem integrable_negative_power_physical_flux_and_bound {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ}
    {c C K ell upper p : ℝ} (hc : 0 < c) (hell : 0 < ell) (hp : 0 < p)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ)
    (hcoeff : ∀ᵐ x ∂μ, (∀ i j, a i j x = a j i x) ∧ ∀ ξ : ι → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ) :
    let D := fun x => 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u x + c) ^ (-p / 2 - 1) * g i x))
    let F := fun x => ∑ i, (∑ j, a i j x * g j x) *
      (η x ^ 2 * (-p - 1) * (u x + c) ^ (-p - 2) * g i x +
        (2 * η x * d i x) * (u x + c) ^ (-p - 1))
    let R := fun x => 2 * upper * (u x + c) ^ (-p) *
      coordinateNormSq (fun i => d i x)
    Integrable D μ ∧ Integrable F μ ∧ Integrable R μ ∧
      (∫ x, D x ∂μ) ≤ -p * (∫ x, F x ∂μ) + ∫ x, R x ∂μ := by
  dsimp only
  obtain ⟨hD, hF, hR, hbound⟩ := integrable_negative_power_spatial_energy_and_bound
    hc hell hp hu hupos hη hηbound ha hb hg hd hcoeff
  have hflux := hupos.mono fun x hx => negative_power_weighted_flux_eq
    (fun i j => a i j x) (fun i => g i x) (fun i => d i x)
    (by linarith : 0 < u x + c) p (η x)
  have hcut := hupos.mono fun x hx => negative_power_weighted_coordinate_norm_sq
    (fun i => d i x) (by linarith : 0 < u x + c) p
  have hFeq := hflux
  have hReq : (fun x => 2 * upper * coordinateNormSq
      (fun i => (u x + c) ^ (-p / 2) * d i x)) =ᵐ[μ]
      (fun x => 2 * upper * (u x + c) ^ (-p) * coordinateNormSq (fun i => d i x)) := by
    filter_upwards [hcut] with x hx
    rw [hx]
    ring
  have hphysical := hF.congr hFeq |>.neg
  refine ⟨hD, ?_, hR.congr hReq, ?_⟩
  · exact hphysical.congr (Filter.Eventually.of_forall fun x => neg_neg _)
  · rw [integral_congr_ae hFeq, integral_congr_ae hReq, integral_neg] at hbound
    simpa only [mul_neg, neg_mul] using hbound

end HeatKernel
