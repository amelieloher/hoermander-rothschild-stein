-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BoundedSquares
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Ring

/-! # The concrete horizontal energy density -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The Lebesgue density of the horizontal energy measure. -/
def horizontalEnergyDensity (u v : energyGraph U X) (x : Fin N → ℝ) : ℝ :=
  ∑ i, (u : GradientSpace U q).snd i x * (v : GradientSpace U q).snd i x

/-- Horizontal energy densities are integrable. -/
theorem integrable_horizontalEnergyDensity (u v : energyGraph U X) :
    Integrable (horizontalEnergyDensity U X u v) (volume.restrict (U : Set (Fin N → ℝ))) := by
  apply integrable_finsetSum
  intro i _
  exact (Lp.memLp ((u : GradientSpace U q).snd i)).integrable_mul
    (Lp.memLp ((v : GradientSpace U q).snd i))

/-- Integrating the concrete density recovers the form. -/
theorem horizontalEnergy_eq_integral_density (u v : energyGraph U X) :
    horizontalEnergy U X u v = ∫ x, horizontalEnergyDensity U X u v x
      ∂volume.restrict (U : Set (Fin N → ℝ)) := by
  simp only [horizontalEnergy, energyGradient_apply, PiLp.inner_apply, horizontalEnergyDensity]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring
  · intro i _
    exact (Lp.memLp ((u : GradientSpace U q).snd i)).integrable_mul
      (Lp.memLp ((v : GradientSpace U q).snd i))

end HeatKernel
