-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerFluxCoordinates
public import HeatKernel.Moser.NegativePowerSobolevCurve
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Product-gradient energy of reciprocal half-power Sobolev curves. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- The full reciprocal half-power product gradient is bounded by its principal
energy and cutoff-gradient moment with constants independent of the exponent. -/
theorem negative_half_power_product_gradient_energy_le {ι : Type*} [Fintype ι]
    (g d : ι → ℝ) {s : ℝ} (hs : 0 < s) (p η : ℝ) :
    coordinateNormSq (fun i => η * (((-p / 2) * s ^ (-p / 2 - 1)) * g i) +
      d i * s ^ (-p / 2)) ≤
      2 * (p / 2) ^ 2 * coordinateNormSq (fun i => η * (s ^ (-p / 2 - 1) * g i)) +
        2 * s ^ (-p) * coordinateNormSq d := by
  rw [mul_assoc 2 (s ^ (-p)) (coordinateNormSq d),
    ← negative_power_weighted_coordinate_norm_sq d hs p]
  simp only [coordinateNormSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := add_sq_le (a := η * (((-p / 2) * s ^ (-p / 2 - 1)) * g i))
    (b := d i * s ^ (-p / 2))
  convert h using 1; ring

/-- Original square-integrable gradients give an integrable full Sobolev
product-gradient energy. Its integral is controlled by the two terms already
present in the reciprocal-power diffusion and spatial cutoff budget. -/
theorem integrable_negative_half_power_product_gradient_energy_and_bound {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {u η : α → ℝ} {g d : ι → α → ℝ} {c K p : ℝ}
    (hc : 0 < c) (hp : 0 < p)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    let A := fun x => (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u x + c) ^ (-p / 2 - 1) * g i x))
    let B := fun x => (u x + c) ^ (-p) * coordinateNormSq (fun i => d i x)
    let E := fun x => coordinateNormSq (fun i => η x *
      (((-p / 2) * (u x + c) ^ (-p / 2 - 1)) * g i x) +
        d i x * (u x + c) ^ (-p / 2))
    Integrable A μ ∧ Integrable B μ ∧ Integrable E μ ∧
      (∫ x, E x ∂μ) ≤ 2 * (∫ x, A x ∂μ) + 2 * (∫ x, B x ∂μ) := by
  dsimp only
  let v := fun i x => η x * ((u x + c) ^ (-p / 2 - 1) * g i x)
  let w := fun i x => (u x + c) ^ (-p / 2) * d i x
  have hv (i : ι) : MemLp (v i) 2 μ :=
    memLp_two_mul_of_ae_bound hη
      (memLp_shifted_nonpositive_power_mul hc (by linarith) hu hupos (hg i)) hηbound
  have hw (i : ι) : MemLp (w i) 2 μ :=
    memLp_shifted_nonpositive_power_mul hc (by linarith) hu hupos (hd i)
  have hvsq : Integrable (fun x => coordinateNormSq (fun i => v i x)) μ := by
    unfold coordinateNormSq
    exact integrable_finsetSum _ fun i _ => (hv i).integrable_sq
  have hwsq : Integrable (fun x => coordinateNormSq (fun i => w i x)) μ := by
    unfold coordinateNormSq
    exact integrable_finsetSum _ fun i _ => (hw i).integrable_sq
  have hA := hvsq.const_mul ((p / 2) ^ 2)
  have hB : Integrable (fun x => (u x + c) ^ (-p) * coordinateNormSq (fun i => d i x)) μ := by
    apply hwsq.congr
    filter_upwards [hupos] with x hx
    exact negative_power_weighted_coordinate_norm_sq _ (by linarith : 0 < u x + c) p
  have hE : Integrable (fun x => coordinateNormSq (fun i => η x *
      (((-p / 2) * (u x + c) ^ (-p / 2 - 1)) * g i x) +
        d i x * (u x + c) ^ (-p / 2))) μ := by
    unfold coordinateNormSq
    apply integrable_finsetSum
    intro i _
    have hi := ((hv i).const_mul (-p / 2) |>.add (hw i)).integrable_sq
    apply hi.congr
    exact Filter.Eventually.of_forall fun x => by
      simp only [Pi.add_def, v, w]
      ring
  refine ⟨hA, hB, hE, ?_⟩
  have hbound := integral_mono_ae hE ((hA.const_mul 2).add (hB.const_mul 2)) (by
    filter_upwards [hupos] with x hx
    simpa only [Pi.add_apply, v, mul_assoc] using
      negative_half_power_product_gradient_energy_le (fun i => g i x) (fun i => d i x)
        (by linarith : 0 < u x + c) p (η x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul, integral_const_mul] at hbound
  simpa only [integral_const_mul, v] using hbound

end HeatKernel
