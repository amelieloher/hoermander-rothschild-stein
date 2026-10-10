-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientEnergy
import Mathlib.Tactic.Linter

/-! # Spatial L² flux representation of horizontal forms -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace

namespace HeatKernel

/-- A spatial L² matrix-flux representative identifies the coefficient form with the Hilbert
pairing against the test gradient. -/
theorem coefficientEnergy_eq_inner_flux {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) (u v : energyGraph U X)
    (J : PiLp 2 (fun _ : Fin q => SpatialL2 U))
    (hJ : ∀ i, J i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => ∑ j, a i j x * (u : GradientSpace U q).snd j x) :
    coefficientEnergy U X a u v = inner ℝ J (energyGradient U X v) := by
  have H : coefficientEnergyDensity U X a u v =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => ∑ i, J i x * (v : GradientSpace U q).snd i x := by
    filter_upwards [ae_all_iff.mpr hJ] with x hx
    simp only [coefficientEnergyDensity, hx, Finset.sum_mul]
  unfold coefficientEnergy
  rw [integral_congr_ae H, integral_finsetSum]
  · simp only [energyGradient_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    exact .of_forall fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring
  · intro i _
    exact (Lp.memLp (J i)).integrable_mul (Lp.memLp ((v : GradientSpace U q).snd i))



end HeatKernel
