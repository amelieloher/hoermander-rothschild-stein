-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.SecondCommutator

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem operatorComm_sum_right {κ : Type*} (I : Finset κ) (A : Operator N) (T : κ → Operator N) :
    operatorComm A (∑ k ∈ I, T k) = ∑ k ∈ I, operatorComm A (T k) := by
  classical
  induction I using Finset.induction_on with
  | empty => ext u; simp [operatorComm]
  | insert k I hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, operatorComm_add_right, ih]

theorem operatorComm_sum_left {κ : Type*} (I : Finset κ) (T : κ → Operator N) (B : Operator N) :
    operatorComm (∑ k ∈ I, T k) B = ∑ k ∈ I, operatorComm (T k) B := by
  classical
  induction I using Finset.induction_on with
  | empty => ext u; simp [operatorComm]
  | insert k I hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, operatorComm_add_left, ih]

theorem vectorFieldOperator_eq_sum (V : RealSchwartzVectorField N) :
    vectorFieldOperator V = ∑ i : Fin N, DOp (complexifyRealSchwartz (V i)) i := rfl

/-- The first mollifier commutator with a real Schwartz vector
field is of order zero uniformly in the scale. -/
theorem uniformOrder_comm_moll_vectorField (X : RealSchwartzVectorField N) :
    UniformOrder 0 (fun d : PosScale => operatorComm (mollOpS N d) (vectorFieldOperator X)) := by
  have : (fun d : PosScale => operatorComm (mollOpS N d) (vectorFieldOperator X)) =
      fun d => ∑ i : Fin N, operatorComm (mollOpS N d) (DOp (complexifyRealSchwartz (X i)) i) := by
    funext d
    rw [vectorFieldOperator_eq_sum, operatorComm_sum_right]
  rw [this]
  exact UniformOrder.sum _ _ fun i _ => uniformOrder_comm_moll_DOp _ i

/-- The double mollifier commutator with two real Schwartz vector
fields is of order zero uniformly in the scale. -/
theorem uniformOrder_comm2_moll_vectorField (X Y : RealSchwartzVectorField N) :
    UniformOrder 0 (fun d : PosScale =>
      operatorComm (operatorComm (mollOpS N d) (vectorFieldOperator X)) (vectorFieldOperator Y)) := by
  have : (fun d : PosScale =>
      operatorComm (operatorComm (mollOpS N d) (vectorFieldOperator X)) (vectorFieldOperator Y)) =
      fun d => ∑ i : Fin N, ∑ k : Fin N, operatorComm
        (operatorComm (mollOpS N d) (DOp (complexifyRealSchwartz (X i)) i))
        (DOp (complexifyRealSchwartz (Y k)) k) := by
    funext d
    rw [vectorFieldOperator_eq_sum, vectorFieldOperator_eq_sum]
    simp only [operatorComm_sum_right, operatorComm_sum_left]
    exact Finset.sum_comm
  rw [this]
  exact UniformOrder.sum _ _ fun i _ => UniformOrder.sum _ _ fun k _ =>
    uniformOrder_comm2_moll_DOp _ _ i k

end Hormander.B
