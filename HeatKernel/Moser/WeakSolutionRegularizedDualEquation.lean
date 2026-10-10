-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionTimePairIntegrability
public import HeatKernel.Form.TimeAverageIntegrability
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # The regularized dual time equation

Smooth backward time tests turn a local weak time balance into an almost
everywhere forward difference equation, with equality in the continuous dual.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- Backward time tests give the integrated forward difference equation on a
buffered interval. -/
theorem SatisfiesDualTimeBalance.integral_forward_difference_eq_on_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D F : ℝ → (E →L[ℝ] ℝ)} {a b h : ℝ}
    (hbalance : SatisfiesDualTimeBalance (Icc a b) D F)
    (hD : LocallyIntegrable D volume)
    (hDs : LocallyIntegrable (fun t => D (t + h)) volume) (hiF : Integrable F)
    (hh : 0 ≤ h) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo a (b - h)) :
    (∫ t, ψ t • (h⁻¹ • (D (t + h) - D t))) =
      -(∫ t, ψ t • forwardTimeAverage h F t) := by
  have hs' : tsupport ψ ⊆ Icc a (b - h) := hs.trans Ioo_subset_Icc_self
  have havgs : tsupport (backwardTimeAverage h ψ) ⊆ Icc a b := by
    simpa only [sub_add_cancel] using tsupport_backwardTimeAverage_subset hs' hh
  have he := hbalance (backwardTimeAverage h ψ) (contDiff_backwardTimeAverage hψ h)
    (hasCompactSupport_backwardTimeAverage hs' hh) havgs
  have hl : (∫ t in Icc a b, deriv (backwardTimeAverage h ψ) t • D t) =
      ∫ t, deriv (backwardTimeAverage h ψ) t • D t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [deriv_of_notMem_tsupport (fun hm => ht (havgs hm)), zero_smul]
  have hr : (∫ t in Icc a b, backwardTimeAverage h ψ t • F t) =
      ∫ t, backwardTimeAverage h ψ t • F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (havgs hm)), zero_smul]
  have hder : deriv (backwardTimeAverage h ψ) =
      fun t => h⁻¹ • (ψ t - ψ (t - h)) := funext fun t =>
    (hasDerivAt_backwardTimeAverage_of_continuous hψ.continuous h t).deriv
  have hzero := hD.integrable_smul_left_of_hasCompactSupport
    hψ.continuous hc
  have hshift := hDs.integrable_smul_left_of_hasCompactSupport
    hψ.continuous hc
  have heq := he.2.2.1
  rw [hl, hr, hder, integral_backward_difference_quotient_test h hzero hshift,
    integral_backwardTimeAverage_smul_eq_of_integrable hiF hψ.continuous hc h] at heq
  simpa only [neg_neg] using congrArg Neg.neg heq

/-- A local dual weak balance gives the regularized dual equation on the interval
whose forward averaging segments remain inside the time domain. -/
theorem SatisfiesDualTimeBalance.ae_forward_difference_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {D F : ℝ → (E →L[ℝ] ℝ)} {a b h : ℝ}
    (hbalance : SatisfiesDualTimeBalance (Icc a b) D F)
    (hD : MemLp D 2 volume) (hF : MemLp F 2 volume) (hiF : Integrable F)
    (hh : 0 ≤ h) :
    ∀ᵐ t ∂volume, t ∈ Ioo a (b - h) →
      h⁻¹ • (D (t + h) - D t) = -forwardTimeAverage h F t := by
  have hDs := hD.comp_measurePreserving (measurePreserving_add_right volume h)
  have hdiff : MemLp (fun t => h⁻¹ • (D (t + h) - D t)) 2 volume :=
    (hDs.sub hD).const_smul h⁻¹
  have havg : MemLp (forwardTimeAverage h F) 2 volume :=
    memLp_forwardDualTimeAverage (V := E) hF hh
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hid : LocallyIntegrable (fun t => h⁻¹ • (D (t + h) - D t)) volume :=
    hdiff.locallyIntegrable hp
  have hia : LocallyIntegrable (forwardTimeAverage h F) volume :=
    havg.locallyIntegrable hp
  have hres := hid.sub hia.neg
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a (b - h) →
      (h⁻¹ • (D (t + h) - D t) - (-forwardTimeAverage h F t)) = 0 :=
    isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hres.locallyIntegrableOn (Ioo a (b - h))) ?_
  · filter_upwards [hz] with t ht
    intro hm
    exact sub_eq_zero.mp (ht hm)
  intro ψ hψ hc hs
  have heq := hbalance.integral_forward_difference_eq_on_interval
    (hD.locallyIntegrable hp) (hDs.locallyIntegrable hp) hiF hh hψ hc hs
  have hsplit : (fun t => ψ t •
      (h⁻¹ • (D (t + h) - D t) - (-forwardTimeAverage h F t))) =
      (fun t => ψ t • (h⁻¹ • (D (t + h) - D t)) - ψ t • (-forwardTimeAverage h F t)) :=
    funext fun t => smul_sub _ _ _
  have hi1 : Integrable (fun t => ψ t • (h⁻¹ • (D (t + h) - D t))) :=
    hid.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
  have hi2 : Integrable (fun t => ψ t • (-forwardTimeAverage h F t)) := by
    simpa only [Pi.neg_apply] using
      hia.neg.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
  rw [hsplit, integral_sub hi1 hi2]
  simp_rw [smul_neg, integral_neg]
  exact sub_eq_zero.mpr heq

end HeatKernel
