-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionEnergyRepresentatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith

/-! Backward time budgets for concave-power energies. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory

namespace HeatKernel

/-- A cutoff vanishing at the upper time gives a lower-endpoint energy
budget when the energy derivative dominates diffusion minus the cutoff error. -/
theorem reverse_holder_time_weighted_energy_budget
    {e F D R χ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : AbsolutelyContinuousOnInterval e a b)
    (hder : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt e (F t) t)
    (hF : IntervalIntegrable F volume a b)
    (hD : IntervalIntegrable D volume a b)
    (hR : IntervalIntegrable R volume a b)
    (habs : ∀ᵐ t ∂volume, D t ≤ F t + R t)
    (hχ : ContDiff ℝ 1 χ) (hχb : χ b = 0)
    (hχpos : ∀ᵐ t ∂volume, 0 ≤ χ t) :
    χ a * e a + (∫ t in a..b, χ t * D t) ≤
      (∫ t in a..b, -(deriv χ t) * e t) + ∫ t in a..b, χ t * R t := by
  have hχF := hF.continuousOn_mul hχ.continuous.continuousOn
  have hχD := hD.continuousOn_mul hχ.continuous.continuousOn
  have hχR := hR.continuousOn_mul hχ.continuous.continuousOn
  have hχe : IntervalIntegrable (fun t => deriv χ t * e t) volume a b :=
    ((hχ.continuous_deriv (by norm_num)).continuousOn.mul he.continuousOn).intervalIntegrable
  have hp : AbsolutelyContinuousOnInterval (fun t => χ t * e t) a b := by
    simpa only [Pi.mul_def] using hχ.contDiffOn.absolutelyContinuousOnInterval.mul he
  have hid : (∫ t in a..b, deriv χ t * e t + χ t * F t) = -(χ a * e a) := by
    have hFTC : (∫ t in a..b, deriv (fun s => χ s * e s) t) = -(χ a * e a) := by
      simpa only [hχb, zero_mul, zero_sub] using hp.integral_deriv_eq_sub
    rw [← hFTC]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hder] with t ht
    intro hm
    have hd := (hχ.differentiable (by norm_num) t).hasDerivAt.mul
      (ht (uIoc_subset_uIcc hm))
    have hd' : deriv (fun t => χ t * e t) t = deriv χ t * e t + χ t * F t := by
      simpa only [Pi.mul_def, mul_neg, sub_eq_add_neg] using hd.deriv
    exact hd'.symm
  rw [intervalIntegral.integral_add hχe hχF] at hid
  have hbound := intervalIntegral.integral_mono_ae hab hχD (hχF.add hχR) (by
    filter_upwards [habs, hχpos] with t ht hpt
    simpa only [mul_add] using mul_le_mul_of_nonneg_left ht hpt)
  rw [intervalIntegral.integral_add hχF hχR] at hbound
  have hneg : (∫ t in a..b, -(deriv χ t) * e t) =
      -(∫ t in a..b, deriv χ t * e t) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  rw [hneg]
  linarith

/-- The same time representative gives backward budgets at every lower endpoint
of the tested interval. -/
theorem reverse_holder_time_weighted_initial_budgets
    {e F D R χ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : AbsolutelyContinuousOnInterval e a b)
    (hder : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt e (F t) t)
    (hF : IntervalIntegrable F volume a b)
    (hD : IntervalIntegrable D volume a b)
    (hR : IntervalIntegrable R volume a b)
    (habs : ∀ᵐ t ∂volume, D t ≤ F t + R t)
    (hχ : ContDiff ℝ 1 χ) (hχb : χ b = 0)
    (hχpos : ∀ᵐ t ∂volume, 0 ≤ χ t) :
    ∀ s ∈ Icc a b, χ s * e s + (∫ t in s..b, χ t * D t) ≤
      (∫ t in s..b, -(deriv χ t) * e t) + ∫ t in s..b, χ t * R t := by
  intro s hs
  have hsub : uIcc s b ⊆ uIcc a b := by
    rw [uIcc_of_le hs.2, uIcc_of_le hab]
    exact Icc_subset_Icc_left hs.1
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc s b → HasDerivAt e (F t) t := by
    filter_upwards [hder] with t ht
    exact fun hm => ht (hsub hm)
  exact reverse_holder_time_weighted_energy_budget hs.2 (he.mono hsub) hd
    (hF.mono_set hsub) (hD.mono_set hsub) (hR.mono_set hsub) habs hχ hχb hχpos

end HeatKernel
