-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Calculus.ContDiff.Basic

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import all Mathlib.Analysis.InnerProductSpace.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.RCLike.Basic
import all Mathlib.Analysis.InnerProductSpace.Defs
import all Mathlib.Analysis.Normed.Module.Basic
import all Mathlib.Analysis.Normed.Field.Basic

/-! # Scalar energy representatives and compact temporal tests

An almost-everywhere endpoint equality with an integrable flux gives an absolutely
continuous representative of the scalar energy. Integration by parts then permits
smooth temporal weights without imposing endpoint values on the original curve.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
namespace HeatKernel

/-- On an interior time interval, an energy with an almost-everywhere endpoint
equality has an absolutely continuous representative with derivative minus the flux.
This assertion concerns an equality, rather than a general subsolution inequality. -/
theorem exists_absolutelyContinuous_energy_representative_of_ae_endpoint_identity
    {E f : ℝ → ℝ} {A B a b : ℝ}
    (hf : IntegrableOn f (Icc A B)) (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    (he : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ≤ t → A < s → t < B → E s - E t = ∫ r in Icc s t, f r) :
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e A B ∧
      e =ᵐ[volume.restrict (Icc a b)] E ∧
      (∀ᵐ t ∂volume, t ∈ Icc A B → HasDerivAt e (-f t) t) := by
  have hAB : A ≤ B := by linarith
  obtain ⟨s, hs, hsAa⟩ := (Measure.dense_of_ae he).exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr hAa)
  have hsAB : s ∈ uIcc A B := by
    rw [uIcc_of_le hAB]
    exact ⟨hsAa.1.le, (hsAa.2.le.trans hab).trans hbB.le⟩
  have hfi : IntervalIntegrable f volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hf
  let e : ℝ → ℝ := fun t => E s - ∫ r in s..t, f r
  refine ⟨e, ?_, ?_, ?_⟩
  · have hc : ContDiff ℝ 1 (fun _ : ℝ => E s) := contDiff_const
    exact hc.contDiffOn.absolutelyContinuousOnInterval.sub
      (hfi.absolutelyContinuousOnInterval_intervalIntegral hsAB)
  · filter_upwards [ae_restrict_of_ae hs, self_mem_ae_restrict measurableSet_Icc] with t ht htab
    have hst : s ≤ t := hsAa.2.le.trans htab.1
    have hid := ht hst hsAa.1 (htab.2.trans_lt hbB)
    have hint : (∫ r in s..t, f r) = ∫ r in Icc s t, f r := by
      rw [intervalIntegral.integral_of_le hst, integral_Icc_eq_integral_Ioc]
    dsimp [e]
    rw [hint]
    linarith
  · filter_upwards [hfi.ae_hasDerivAt_integral] with t ht htab
    have hd := ht (by simpa only [uIcc_of_le hAB] using htab) s hsAB
    convert! hd.const_sub (E s) using 1

end HeatKernel
