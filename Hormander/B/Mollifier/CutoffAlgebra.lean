-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.Uncut
public import Hormander.B.Multipliers

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem multiplierOperator_comm (g h : TestFunction N) :
    operatorComm (multiplierOperator g) (multiplierOperator h) = 0 := by
  apply operatorComm_eq_zero_of_comm
  rw [multiplierOperator_comp, multiplierOperator_comp]
  congr 1
  ext x
  simp only [multiplierOperator_apply]
  ring

theorem vectorFieldOperator_apply (V : RealSchwartzVectorField N) (g : TestFunction N)
    (x : Carrier N) :
    vectorFieldOperator V g x =
      ∑ i : Fin N, (V i x : ℂ) * coordinateDerivative i g x := by
  unfold vectorFieldOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, realMultiplierOperator]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [multiplierOperator_apply]
  rfl


theorem coordinateDerivative_mul_apply (i : Fin N) (g u : TestFunction N) (x : Carrier N) :
    coordinateDerivative i (multiplierOperator g u) x =
      coordinateDerivative i g x * u x + g x * coordinateDerivative i u x := by
  have h := LinearMap.congr_fun (operatorComm_coordinateDerivative_multiplier i g) u
  have hx := congrArg (fun w : TestFunction N => w x) h
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, sub_apply,
    multiplierOperator_apply] at hx
  linear_combination hx

/-- Leibniz rule for a Schwartz vector field acting on a product with a multiplier. -/
theorem operatorComm_vectorField_multiplier (X : RealSchwartzVectorField N) (g : TestFunction N) :
    operatorComm (vectorFieldOperator X) (multiplierOperator g) =
      multiplierOperator (vectorFieldOperator X g) := by
  ext u x
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, sub_apply,
    multiplierOperator_apply, vectorFieldOperator_apply, coordinateDerivative_mul_apply,
    Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The exact one-step cutoff identity, given the Leibniz relation `[V, M₁] = Mv`. -/
theorem comm_cutoff_identity (S V M1 Mv : Operator N)
    (hv : ∀ w, V (M1 w) - M1 (V w) = Mv w) :
    operatorComm (S.comp M1) V = (operatorComm S V).comp M1 - S.comp Mv := by
  ext u : 1
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [← hv u, map_sub]
  abel

/-- The exact two-step cutoff identity, given `[V, M₁] = Mv` and `[V, Mv] = Mw`. -/
theorem comm2_cutoff_identity (S V M1 Mv Mw : Operator N)
    (hv : ∀ w, V (M1 w) - M1 (V w) = Mv w) (hw : ∀ w, V (Mv w) - Mv (V w) = Mw w) :
    operatorComm (operatorComm (S.comp M1) V) V =
      (operatorComm (operatorComm S V) V).comp M1 - (2 : ℂ) • (operatorComm S V).comp Mv +
        S.comp Mw := by
  ext u : 1
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply]
  rw [← hw u, ← hv u, ← hv (V u)]
  simp only [map_sub]
  rw [two_smul]
  abel

end Hormander.B
