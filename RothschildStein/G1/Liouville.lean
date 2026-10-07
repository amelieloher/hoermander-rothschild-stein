-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.DeterminantDerivative
public import RothschildStein.G1.LocalFlows
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- The scalar linear ODE with initial value one is the exponential of
its oriented coefficient integral (BB pp. 3–4, 89–90). -/
theorem scalarODE_eq_exp_integral {a b : ℝ} {c f : ℝ → ℝ}
    (hc : ContinuousOn c (Ioo a b)) (hzero : (0 : ℝ) ∈ Ioo a b)
    (hf : ∀ v ∈ Ioo a b, HasDerivAt f (c v * f v) v) (hf₀ : f 0 = 1)
    {t : ℝ} (ht : t ∈ Ioo a b) : f t = Real.exp (∫ v in 0..t, c v) := by
  let C := fun v => ∫ w in 0..v, c w
  have hC : ∀ v ∈ Ioo a b, HasDerivAt C (c v) v := by
    intro v hv
    have hint : IntervalIntegrable c volume 0 v := (hc.mono (ordConnected_Ioo.uIcc_subset hzero hv)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_right hint
      (hc.stronglyMeasurableAtFilter isOpen_Ioo v hv)
      (hc.continuousAt (isOpen_Ioo.mem_nhds hv))
  have hprod : ∀ v ∈ Ioo a b, HasDerivAt (fun w => Real.exp (-C w) * f w) 0 v := by
    intro v hv
    convert (((hC v hv).neg.exp).mul (hf v hv)) using 1
    ring
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun v hv => (hprod v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hprod v hv).deriv) ht hzero
  have hfactor : Real.exp (-C t) * f t = 1 := by simpa [C, hf₀] using heq
  have hcancel : Real.exp (C t) * Real.exp (-C t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    f t = (Real.exp (C t) * Real.exp (-C t)) * f t := by rw [hcancel, one_mul]
    _ = Real.exp (C t) := by rw [mul_assoc, hfactor, mul_one]

/-- Liouville's formula for an actual matrix variational solution, with
no invertibility hypothesis. The exponential formula implies positivity
(with the coordinate-divergence convention of BB Prop 2.22, pp. 89–90). -/
theorem matrixODE_det_eq_exp_integral {N : ℕ} {a b : ℝ}
    {A M : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hA : ContinuousOn A (Ioo a b)) (hzero : (0 : ℝ) ∈ Ioo a b)
    (hM : ∀ v ∈ Ioo a b, HasDerivAt M (A v * M v) v) (hM₀ : M 0 = 1)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    (M t).det = Real.exp (∫ v in 0..t, (A v).trace) := by
  have htrace : ContinuousOn (fun v => (A v).trace) (Ioo a b) := by
    apply continuousOn_finsetSum
    intro i hi
    exact (continuous_apply i).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hA)
  exact scalarODE_eq_exp_integral htrace hzero
    (fun v hv => matrixODE_det_hasDerivAt (hM v hv))
    (by rw [hM₀, Matrix.det_one]) ht

end RothschildStein.G1
