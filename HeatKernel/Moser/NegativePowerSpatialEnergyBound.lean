-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerFluxIntegrability
public import HeatKernel.Moser.NegativePowerMatrixCoercivity
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Integrated reciprocal-power spatial energy from original square-integrable gradients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- The original square-integrable gradients give integrable negative half-power
horizontal energy and its coefficient-form absorption bound. The positive shift
and ellipticity control all terms; no nonlinear energy integrability is assumed. -/
theorem integrable_negative_power_spatial_energy_and_bound {α ι : Type*}
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
    let v := fun i x => η x * ((u x + c) ^ (-p / 2 - 1) * g i x)
    let w := fun i x => (u x + c) ^ (-p / 2) * d i x
    let D := fun x => 2 * ell * (p / 2) ^ 2 * coordinateNormSq (fun i => v i x)
    let F := fun x => (p + 1) * matrixEnergy (fun i j => a i j x) (fun i => v i x) -
      2 * (∑ i, ∑ j, a i j x * v j x * w i x)
    let R := fun x => 2 * upper * coordinateNormSq (fun i => w i x)
    Integrable D μ ∧ Integrable F μ ∧ Integrable R μ ∧
      (∫ x, D x ∂μ) ≤ p * (∫ x, F x ∂μ) + ∫ x, R x ∂μ := by
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
    apply integrable_finsetSum
    intro i _
    exact (hv i).integrable_sq
  have hwsq : Integrable (fun x => coordinateNormSq (fun i => w i x)) μ := by
    unfold coordinateNormSq
    apply integrable_finsetSum
    intro i _
    exact (hw i).integrable_sq
  have hD := hvsq.const_mul (2 * ell * (p / 2) ^ 2)
  have hF := (integrable_matrix_pairing ha hb hv hv).const_mul (p + 1) |>.sub
    ((integrable_matrix_pairing ha hb hv hw).const_mul 2)
  have hR := hwsq.const_mul (2 * upper)
  refine ⟨hD, hF, hR, ?_⟩
  have hbound := integral_mono_ae hD ((hF.const_mul p).add hR) (by
    filter_upwards [hcoeff] with x hx
    have hpos (ξ : ι → ℝ) : 0 ≤ matrixEnergy (fun i j => a i j x) ξ := by
      have hn : 0 ≤ coordinateNormSq ξ := by
        unfold coordinateNormSq
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact (mul_nonneg hell.le hn).trans (hx.2 ξ).1
    have h := negative_power_matrix_half_power_flux (fun i j => a i j x) hx.1 hpos
      hell hp zero_lt_one 1 (fun i => v i x) (fun i => w i x)
      (hx.2 _).1 (hx.2 _).2
    simpa only [Real.one_rpow, mul_one, one_pow, Pi.add_apply, Pi.sub_apply, matrixEnergy] using h)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hF.const_mul p) hR, integral_const_mul] at hbound
  simpa only [integral_const_mul, Pi.sub_apply, matrixEnergy, v, w] using hbound

end HeatKernel
