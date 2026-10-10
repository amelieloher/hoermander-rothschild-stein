-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValuePowerFluxCoercivity
public import HeatKernel.Moser.CaccioppoliSpatialPowerTest
public import HeatKernel.Moser.WeakSolutionSpatialTransport
public import HeatKernel.Moser.MeanValueTerminalEnergy
public import HeatKernel.Moser.MeanValueEnergyIntegrability
public import HeatKernel.Form.TimeDependentEnergyPairings
public import HeatKernel.Sobolev.GradientRepresentativeMoments
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Positive-power terminal energy estimates for identity coefficients -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A square-weighted identity coefficient form is the literal cutoff gradient energy. -/
theorem square_weighted_identity_coefficientEnergy_eq_integral {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (η : (Fin N → ℝ) → ℝ)
    (z : energyGraph (N := N) ⊤ X) :
    coefficientEnergy ⊤ X (fun i j x => η x ^ 2 * if i = j then 1 else 0) z z =
      ∫ x, ∑ i, (η x * (z : GradientSpace (N := N) ⊤ q).snd i x) ^ 2 := by
  simp only [coefficientEnergy, coefficientEnergyDensity, Opens.coe_top, Measure.restrict_univ]
  congr 1
  funext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

end HeatKernel
