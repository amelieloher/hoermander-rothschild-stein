-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Multipliers
public import Hormander.B.Fractional.DiffOps

@[expose] public section

noncomputable section

namespace Hormander.B

/-- The zero operator is differential of every nonnegative degree. -/
theorem isDiffOp_zero {N : ℕ} (m : ℕ) : IsDiffOp m (0 : Operator N) := by
  simpa only [multiplierOperator_zero] using IsDiffOp.mult m (0 : TestFunction N)

/-- Finite sums retain a common differential degree. -/
theorem isDiffOp_sum {N : ℕ} {ι : Type*} (I : Finset ι) (P : ι → Operator N)
    (m : ℕ) (hP : ∀ i ∈ I, IsDiffOp m (P i)) : IsDiffOp m (∑ i ∈ I, P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using isDiffOp_zero (N := N) m
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self i I)).add
      (ih fun j hj => hP j (Finset.mem_insert_of_mem hj))

/-- Move a coordinate derivative past a coefficient. -/
theorem coordinateDerivative_comp_multiplier {N : ℕ} (i : Fin N) (g : TestFunction N) :
    (coordinateDerivative i).comp (multiplierOperator g) =
      (multiplierOperator g).comp (coordinateDerivative i) +
        multiplierOperator (coordinateDerivative i g) := by
  have h := operatorComm_coordinateDerivative_multiplier i g
  unfold operatorComm at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

/-- A Schwartz multiplier on the right retains the differential degree. -/
theorem IsDiffOp.comp_multiplier {N : ℕ} {m : ℕ} {P : Operator N}
    (hP : IsDiffOp m P) (g : TestFunction N) :
    IsDiffOp m (P.comp (multiplierOperator g)) := by
  induction hP generalizing g with
  | mult m a => rw [multiplierOperator_comp]; exact IsDiffOp.mult m _
  | add _ _ ihP ihQ => rw [LinearMap.add_comp]; exact (ihP g).add (ihQ g)
  | @derivRight m P i hP ih =>
    rw [LinearMap.comp_assoc, coordinateDerivative_comp_multiplier, LinearMap.comp_add,
      ← LinearMap.comp_assoc]
    exact ((ih g).derivRight i).add
      ((ih (coordinateDerivative i g)).mono (Nat.le_succ m))

/-- Composition adds differential degrees. -/
theorem IsDiffOp.comp {N : ℕ} {m n : ℕ} {P Q : Operator N}
    (hP : IsDiffOp m P) (hQ : IsDiffOp n Q) : IsDiffOp (m + n) (P.comp Q) := by
  induction hQ with
  | mult n g => exact (hP.comp_multiplier g).mono (Nat.le_add_right m n)
  | add _ _ ihP ihQ => rw [LinearMap.comp_add]; exact ihP.add ihQ
  | derivRight i _ ih =>
    rw [← LinearMap.comp_assoc]
    simpa only [Nat.add_assoc] using ih.derivRight i

/-- The shared real Schwartz vector-field operator is differential of degree one. -/
theorem isDiffOp_vectorFieldOperator {N : ℕ} (V : RealSchwartzVectorField N) :
    IsDiffOp 1 (vectorFieldOperator V) := by
  unfold vectorFieldOperator
  apply isDiffOp_sum
  intro i _
  exact (IsDiffOp.mult 0 (complexifyRealSchwartz (V i))).derivRight i

/-- Scalar multiples preserve differential degree. -/
theorem IsDiffOp.smul {N : ℕ} {m : ℕ} {P : Operator N}
    (h : IsDiffOp m P) (c : ℂ) : IsDiffOp m (c • P) := by
  induction h with
  | mult m g =>
    have e : c • multiplierOperator g = multiplierOperator (c • g) := by
      ext u x
      simp [multiplierOperator_apply, mul_assoc]
    rw [e]; exact IsDiffOp.mult m _
  | add _ _ ihP ihQ => rw [smul_add]; exact ihP.add ihQ
  | derivRight i _ ih =>
    rw [← LinearMap.smul_comp]
    exact ih.derivRight i

/-- Multiplication operators commute. -/
theorem operatorComm_multiplier_multiplier {N : ℕ} (g h : TestFunction N) :
    operatorComm (multiplierOperator g) (multiplierOperator h) = 0 := by
  ext u x
  simp [operatorComm, multiplierOperator_apply, mul_left_comm]

/-- Degree-zero differential operators commute with all multipliers. -/
theorem IsDiffOp.comm_multiplier_zero {N : ℕ} {P : Operator N}
    (h : IsDiffOp 0 P) (g : TestFunction N) :
    operatorComm P (multiplierOperator g) = 0 := by
  have aux : ∀ {m : ℕ} {P : Operator N}, IsDiffOp m P → m = 0 →
      operatorComm P (multiplierOperator g) = 0 := by
    intro m P h
    induction h with
    | mult m a => intro _; exact operatorComm_multiplier_multiplier a g
    | add _ _ ihP ihQ => intro hm; rw [operatorComm_add_left, ihP hm, ihQ hm, add_zero]
    | derivRight i _ _ => intro hm; omega
  exact aux h rfl

/-- A multiplier commutator loses one differential degree. -/
theorem IsDiffOp.comm_multiplier {N : ℕ} {m : ℕ} {P : Operator N}
    (h : IsDiffOp m P) (g : TestFunction N) :
    IsDiffOp (m - 1) (operatorComm P (multiplierOperator g)) := by
  induction h with
  | mult m a => rw [operatorComm_multiplier_multiplier]; exact isDiffOp_zero _
  | add _ _ ihP ihQ => rw [operatorComm_add_left]; exact ihP.add ihQ
  | @derivRight m P i h ih =>
    rw [operatorComm_comp_left, operatorComm_coordinateDerivative_multiplier]
    have hfirst := h.comp_multiplier (coordinateDerivative i g)
    cases m with
    | zero =>
      rw [h.comm_multiplier_zero g, LinearMap.zero_comp, add_zero]
      exact hfirst
    | succ k =>
      exact hfirst.add (by simpa using ih.derivRight i)

/-- Top differential terms cancel in a commutator. -/
theorem IsDiffOp.comm {N : ℕ} {m n : ℕ} {P Q : Operator N}
    (hP : IsDiffOp m P) (hQ : IsDiffOp n Q) :
    IsDiffOp (m + n - 1) (operatorComm P Q) := by
  induction hQ with
  | mult n g => exact (hP.comm_multiplier g).mono (by omega)
  | add _ _ ihQ ihR => rw [operatorComm_add_right]; exact ihQ.add ihR
  | @derivRight n Q i hQ ih =>
    rw [operatorComm_comp_right]
    have hsecond : IsDiffOp (n + m) (Q.comp (operatorComm P (coordinateDerivative i))) := by
      rw [operatorComm_antisymm P]
      exact hQ.comp ((hP.comm_coordinateDerivative i).smul (-1))
    by_cases hz : m + n = 0
    · have hm : m = 0 := by omega
      have hn : n = 0 := by omega
      subst m; subst n
      have he : operatorComm P Q = 0 := by
        have aux : ∀ {n : ℕ} {Q : Operator N}, IsDiffOp n Q → n = 0 →
            operatorComm P Q = 0 := by
          intro n Q h
          induction h with
          | mult n g => intro _; exact hP.comm_multiplier_zero g
          | add _ _ ihQ ihR => intro hn; rw [operatorComm_add_right, ihQ hn, ihR hn, add_zero]
          | derivRight j _ _ => intro hn; omega
        exact aux hQ rfl
      rw [he, LinearMap.zero_comp, zero_add]
      simpa using hsecond
    · have hfirst := ih.derivRight i
      exact (hfirst.mono (by omega)).add (hsecond.mono (by omega))

/-- Degree-zero differential operators commute with each other. -/
theorem IsDiffOp.comm_zero {N : ℕ} {P Q : Operator N}
    (hP : IsDiffOp 0 P) (hQ : IsDiffOp 0 Q) : operatorComm P Q = 0 := by
  have aux : ∀ {n : ℕ} {Q : Operator N}, IsDiffOp n Q → n = 0 →
      operatorComm P Q = 0 := by
    intro n Q h
    induction h with
    | mult n g => intro _; exact hP.comm_multiplier_zero g
    | add _ _ ihQ ihR => intro hn; rw [operatorComm_add_right, ihQ hn, ihR hn, add_zero]
    | derivRight j _ _ => intro hn; omega
  exact aux hQ rfl

/-- A vector-field commutator is multiplication by its action on the coefficient. -/
theorem vectorFieldOperator_comm_multiplier {N : ℕ} (V : RealSchwartzVectorField N)
    (g : TestFunction N) :
    operatorComm (vectorFieldOperator V) (multiplierOperator g) =
      multiplierOperator (vectorFieldOperator V g) := by
  have hsum : ∀ (I : Finset (Fin N)),
      operatorComm (∑ i ∈ I, (realMultiplierOperator (V i)).comp (coordinateDerivative i))
        (multiplierOperator g) =
      ∑ i ∈ I, (realMultiplierOperator (V i)).comp
        (multiplierOperator (coordinateDerivative i g)) := by
    intro I
    induction I using Finset.induction_on with
    | empty => ext u x; simp [operatorComm]
    | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, operatorComm_add_left, ih,
        operatorComm_comp_left, operatorComm_coordinateDerivative_multiplier]
      rw [realMultiplierOperator, operatorComm_multiplier_multiplier, LinearMap.zero_comp, add_zero]
  rw [vectorFieldOperator, hsum]
  ext u x
  simp [realMultiplierOperator, multiplierOperator_apply,
    Finset.sum_mul, mul_assoc]

/-- The same identity for a real Schwartz multiplier. -/
theorem vectorFieldOperator_comm_realMultiplier {N : ℕ} (V : RealSchwartzVectorField N)
    (g : SchwartzMap (Carrier N) ℝ) :
    operatorComm (vectorFieldOperator V) (realMultiplierOperator g) =
      multiplierOperator (vectorFieldOperator V (complexifyRealSchwartz g)) :=
  vectorFieldOperator_comm_multiplier V (complexifyRealSchwartz g)

end Hormander.B
