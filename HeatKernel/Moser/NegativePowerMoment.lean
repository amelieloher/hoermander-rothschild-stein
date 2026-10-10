-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerAffineEnergy
public import HeatKernel.Moser.NegativePowerFluxIntegrability
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Normalization of affine reciprocal-power energies as literal moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- An integrable weight and a positive shift give an integrable nonpositive
power moment without a separate nonlinear integrability assumption. -/
theorem integrable_weighted_shifted_nonpositive_power {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {W u : α → ℝ} {c r : ℝ} (hc : 0 < c) (hr : r ≤ 0)
    (hW : Integrable W μ) (hu : AEStronglyMeasurable u μ)
    (hupos : ∀ᵐ x ∂μ, 0 ≤ u x) :
    Integrable (fun x => W x * (u x + c) ^ r) μ := by
  apply hW.mul_bdd
    (((hu.add aestronglyMeasurable_const).aemeasurable.pow_const r).aestronglyMeasurable)
  filter_upwards [hupos] with x hx
  change ‖(u x + c) ^ r‖ ≤ c ^ r
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (add_nonneg hx hc.le) r)]
  exact Real.rpow_le_rpow_of_nonpos hc (le_add_of_nonneg_left hx) hr

/-- Restoring the constant of integration identifies the corrected affine
energy with the weighted reciprocal-power moment of the energy-space value. -/
theorem negative_power_corrected_energy_eq_moment {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hW : Integrable W.toFun volume) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    c ^ (-p) * (∫ x, W.toFun x) - p * W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
        w (c ^ (-p - 1)) z =
      ∫ x, W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) := by
  have hu : AEStronglyMeasurable ((z : GradientSpace (N := N) ⊤ q).fst) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp ((z : GradientSpace (N := N) ⊤ q).fst)).aestronglyMeasurable
  have hi := integrable_weighted_shifted_nonpositive_power hc (neg_nonpos.mpr hp.le) hW hu hz
  have heq : W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
        w (c ^ (-p - 1)) z =
      (c ^ (-p) * (∫ x, W.toFun x) -
        ∫ x, W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) / p := by
    rw [negative_power_affine_energy_eq W hc hp w hw z hz]
    calc
      _ = ∫ x, (c ^ (-p) * W.toFun x -
          W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) / p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_div, integral_sub (hW.const_mul _) hi, integral_const_mul]
  rw [heq]
  nlinarith [div_mul_cancel₀ (c ^ (-p) * (∫ x, W.toFun x) -
    ∫ x, W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) hp.ne']

end HeatKernel
