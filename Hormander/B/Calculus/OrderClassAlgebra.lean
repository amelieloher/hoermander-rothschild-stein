-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Order
public import Hormander.B.Fractional.DerivativeFacts
public import Hormander.B.Calculus.TransposeAlgebra
public import Hormander.B.Extension.Conjugation

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

theorem operatorComm_add_right_local (P A B : Operator N) :
    operatorComm P (A + B) = operatorComm P A + operatorComm P B := by
  unfold operatorComm
  rw [LinearMap.comp_add, LinearMap.add_comp]
  abel

theorem bilinearPairing_add_left_local (u v w : TestFunction N) :
    bilinearPairing (u + v) w = bilinearPairing u w + bilinearPairing v w := by
  unfold bilinearPairing
  rw [← MeasureTheory.integral_add (integrable_mul_test u w) (integrable_mul_test v w)]
  congr 1
  funext x
  simp [add_mul]

theorem bilinearPairing_add_right_local (u v w : TestFunction N) :
    bilinearPairing u (v + w) = bilinearPairing u v + bilinearPairing u w := by
  unfold bilinearPairing
  rw [← MeasureTheory.integral_add (integrable_mul_test u v) (integrable_mul_test u w)]
  congr 1
  funext x
  simp [mul_add]

theorem bilinearPairing_smul_left_local (c : ℂ) (u v : TestFunction N) :
    bilinearPairing (c • u) v = c * bilinearPairing u v := by
  unfold bilinearPairing
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  simp [mul_assoc]

theorem bilinearPairing_smul_right_local (c : ℂ) (u v : TestFunction N) :
    bilinearPairing u (c • v) = c * bilinearPairing u v := by
  unfold bilinearPairing
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext x
  simp
  ring

theorem HasBilinearTranspose.add_local {At Bt : Operator N} {A B : Operator N}
    (hA : HasBilinearTranspose A At) (hB : HasBilinearTranspose B Bt) :
    HasBilinearTranspose (A + B) (At + Bt) := by
  intro u v
  simp only [LinearMap.add_apply, bilinearPairing_add_left_local,
    bilinearPairing_add_right_local, hA u v, hB u v]

theorem HasBilinearTranspose.smul_local {A At : Operator N} (c : ℂ)
    (hA : HasBilinearTranspose A At) :
    HasBilinearTranspose (c • A) (c • At) := by
  intro u v
  simp only [LinearMap.smul_apply, bilinearPairing_smul_left_local,
    bilinearPairing_smul_right_local, hA u v]

/-- Iterated commutators distribute over sums in their operator argument. -/
theorem iteratedCommutator_add_right (ys : List (OperatorGenerator N))
    (A B : Operator N) :
    iteratedCommutator ys (A + B) =
      iteratedCommutator ys A + iteratedCommutator ys B := by
  induction ys with
  | nil => rfl
  | cons Y ys ih =>
      change operatorComm Y.toOperator (iteratedCommutator ys (A + B)) =
        operatorComm Y.toOperator (iteratedCommutator ys A) +
          operatorComm Y.toOperator (iteratedCommutator ys B)
      rw [ih, operatorComm_add_right_local]

/-- Iterated commutators commute with scalar multiplication in their operator argument. -/
theorem iteratedCommutator_smul_right (ys : List (OperatorGenerator N))
    (c : ℂ) (A : Operator N) :
    iteratedCommutator ys (c • A) = c • iteratedCommutator ys A := by
  induction ys with
  | nil => rfl
  | cons Y ys ih =>
      simp only [iteratedCommutator, ih]
      ext u x
      simp [operatorComm, LinearMap.sub_apply, mul_sub]

theorem iteratedCommutator_zero (ys : List (OperatorGenerator N)) :
    iteratedCommutator ys (0 : Operator N) = 0 := by
  induction ys with
  | nil => rfl
  | cons Y ys ih => simp [iteratedCommutator, operatorComm, ih]

theorem operatorComm_antisymm_local (A B : Operator N) :
    operatorComm A B = -operatorComm B A := by
  ext u
  simp [operatorComm, LinearMap.sub_apply]

/-- The zero operator belongs to every commutator-order class. -/
theorem operatorClass_zero (m : ℝ) : OperatorClass (N := N) m (0 : Operator N) := by
  refine ⟨0, ?_, ?_⟩
  · intro u v
    simp [bilinearPairing]
  · intro ys
    rw [iteratedCommutator_zero]
    exact hasOrder_zero _

/-- Common-order commutator classes are closed under addition. -/
theorem OperatorClass.add {m : ℝ} {A B : Operator N}
    (hA : OperatorClass m A) (hB : OperatorClass m B) : OperatorClass m (A + B) := by
  rcases hA with ⟨At, hAt, hAorders⟩
  rcases hB with ⟨Bt, hBt, hBorders⟩
  refine ⟨At + Bt, hAt.add_local hBt, ?_⟩
  intro ys
  rw [iteratedCommutator_add_right]
  exact (hAorders ys).add (hBorders ys)

/-- Common-order commutator classes are closed under complex scalar multiplication. -/
theorem OperatorClass.smul {m : ℝ} {A : Operator N} (c : ℂ)
    (hA : OperatorClass m A) : OperatorClass m (c • A) := by
  rcases hA with ⟨At, hAt, hAorders⟩
  refine ⟨c • At, hAt.smul_local c, ?_⟩
  intro ys
  rw [iteratedCommutator_smul_right]
  exact (hAorders ys).smul c

/-- Increasing the permitted order preserves a commutator-order class. -/
theorem OperatorClass.mono {m m' : ℝ} {A : Operator N}
    (hA : OperatorClass m A) (hm : m ≤ m') : OperatorClass m' A := by
  rcases hA with ⟨At, hAt, hAorders⟩
  refine ⟨At, hAt, ?_⟩
  intro ys
  apply HasOrder.mono (hAorders ys)
  exact sub_le_sub_right hm _

/-- Extract the order estimate at an arbitrary commutator word. -/
theorem OperatorClass.iterated_order {m : ℝ} {A : Operator N}
    (hA : OperatorClass m A) (ys : List (OperatorGenerator N)) :
    HasOrder (m - (multiplierCount ys : ℝ)) (iteratedCommutator ys A) := by
  rcases hA with ⟨_, _, horders⟩
  exact horders ys

/-- Appending one commutator generator to the input side of an iterated word. -/
theorem iteratedCommutator_append_single (ys : List (OperatorGenerator N))
    (Y : OperatorGenerator N) (T : Operator N) :
    iteratedCommutator ys (operatorComm Y.toOperator T) =
      iteratedCommutator (ys ++ [Y]) T := by
  induction ys with
  | nil => rfl
  | cons Z ys ih =>
      simp only [iteratedCommutator, ih, List.cons_append]

/-- Successive real vector-field commutators preserve order `m`.
This applies to a localized operator once it is placed in `OperatorClass m`. -/
theorem OperatorClass.vectorField_depth_three {m : ℝ} {A : Operator N}
    (hA : OperatorClass m A) (X Y : RealSchwartzVectorField N) :
    HasOrder m (operatorComm (vectorFieldOperator Y) A) ∧
    HasOrder m (operatorComm (vectorFieldOperator X)
      (operatorComm (vectorFieldOperator Y) A)) ∧
    HasOrder m (operatorComm
      (operatorComm (vectorFieldOperator X)
        (operatorComm (vectorFieldOperator Y) A))
      (vectorFieldOperator X)) := by
  have h1 := hA.iterated_order [.vectorField Y]
  have h2 := hA.iterated_order [.vectorField X, .vectorField Y]
  have h3 := hA.iterated_order [.vectorField X, .vectorField X, .vectorField Y]
  have h1' : HasOrder m (iteratedCommutator [.vectorField Y] A) := by
    simpa [multiplierCount, OperatorGenerator.isMultiplier, List.filter] using h1
  have h2' : HasOrder m (iteratedCommutator [.vectorField X, .vectorField Y] A) := by
    simpa [multiplierCount, OperatorGenerator.isMultiplier, List.filter] using h2
  have h3' : HasOrder m (iteratedCommutator
      [.vectorField X, .vectorField X, .vectorField Y] A) := by
    simpa [multiplierCount, OperatorGenerator.isMultiplier, List.filter] using h3
  refine ⟨?_, ?_, ?_⟩
  · simpa [iteratedCommutator, OperatorGenerator.toOperator] using h1'
  · simpa [iteratedCommutator, OperatorGenerator.toOperator] using h2'
  · rw [operatorComm_antisymm_local]
    have hneg := h3'.smul (-1 : ℂ)
    simpa [iteratedCommutator, OperatorGenerator.toOperator] using hneg

end Hormander.B
