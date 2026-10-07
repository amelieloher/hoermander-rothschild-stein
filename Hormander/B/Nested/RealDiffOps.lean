-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.NestedOrder
public import Hormander.B.Fractional.DiffOps
public import Hormander.B.Fractional.DerivativeFacts
public import Hormander.B.Extension.Continuity
public import Hormander.B.Differential

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.B

variable {N : ℕ}

/-- Real-valued Schwartz functions on the Euclidean carrier. -/
abbrev RS (N : ℕ) := SchwartzMap (Carrier N) ℝ

/-- Product of real Schwartz functions. -/
def rmul (a c : RS N) : RS N := SchwartzMap.smulLeftCLM ℝ (⇑a) c

theorem rmul_apply (a c : RS N) (x : Carrier N) : rmul a c x = a x * c x := by
  simp [rmul, SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth]

/-- Coordinate derivative of a real Schwartz function. -/
def rder (j : Fin N) (a : RS N) : RS N := LineDeriv.lineDerivOp (EuclideanSpace.single j (1 : ℝ)) a

theorem realMultiplierOperator_apply (g : RS N) (u : TestFunction N) (x : Carrier N) :
    realMultiplierOperator g u x = (g x : ℂ) * u x := by
  simp only [realMultiplierOperator, multiplierOperator_apply, complexifyRealSchwartz_apply]

theorem realMultiplierOperator_rmul (a c : RS N) :
    realMultiplierOperator (rmul a c) =
      (realMultiplierOperator a).comp (realMultiplierOperator c) := by
  apply LinearMap.ext
  intro u
  ext x
  simp only [LinearMap.comp_apply, realMultiplierOperator_apply, rmul_apply]
  push_cast
  ring

theorem operatorComm_realMultiplier_realMultiplier (g a : RS N) :
    operatorComm (realMultiplierOperator g) (realMultiplierOperator a) = 0 :=
  operatorComm_multiplier_multiplier _ _

theorem operatorComm_coordinateDerivative_realMultiplier (j : Fin N) (a : RS N) :
    operatorComm (coordinateDerivative j) (realMultiplierOperator a) =
      realMultiplierOperator (rder j a) := by
  rw [realMultiplierOperator, operatorComm_coordinateDerivative_multiplier]
  unfold realMultiplierOperator rder
  rw [complexify_lineDeriv]
  rfl

theorem realMultiplierOperator_neg (c : RS N) :
    realMultiplierOperator (-c) = -realMultiplierOperator c := by
  apply LinearMap.ext
  intro u
  ext x
  simp [realMultiplierOperator_apply]

/-- The operator `M_c ∘ ∂_w`. -/
def rTerm (c : RS N) (w : List (Fin N)) : Operator N :=
  (realMultiplierOperator c).comp (derivWord w)

/-- Differential operators with real Schwartz coefficients of order `< k` (finite sums of
`M_c ∘ ∂_w`, `|w| < k`). -/
def IsRealDiffOp (k : ℕ) (P : Operator N) : Prop :=
  ∃ cs : List (RS N × List (Fin N)), (∀ c ∈ cs, c.2.length < k) ∧
    P = (cs.map fun c => rTerm c.1 c.2).sum

theorem IsRealDiffOp.zero (k : ℕ) : IsRealDiffOp k (0 : Operator N) := ⟨[], by simp, by simp⟩

theorem IsRealDiffOp.of_rTerm {k : ℕ} (c : RS N) {w : List (Fin N)} (hw : w.length < k) :
    IsRealDiffOp k (Hormander.B.rTerm c w) :=
  ⟨[(c, w)], by simpa using hw, by simp⟩

theorem IsRealDiffOp.add {k : ℕ} {P Q : Operator N} (hP : IsRealDiffOp k P) (hQ : IsRealDiffOp k Q) :
    IsRealDiffOp k (P + Q) := by
  obtain ⟨cs, hcs, rfl⟩ := hP
  obtain ⟨ds, hds, rfl⟩ := hQ
  refine ⟨cs ++ ds, ?_, by simp [List.sum_append]⟩
  intro c hc
  rcases List.mem_append.mp hc with h | h
  exacts [hcs c h, hds c h]

theorem IsRealDiffOp.mono {k k' : ℕ} {P : Operator N} (h : IsRealDiffOp k P) (hk : k ≤ k') :
    IsRealDiffOp k' P := by
  obtain ⟨cs, hcs, rfl⟩ := h
  exact ⟨cs, fun c hc => lt_of_lt_of_le (hcs c hc) hk, rfl⟩

theorem rTerm_neg (c : RS N) (w : List (Fin N)) : rTerm (-c) w = -rTerm c w := by
  unfold rTerm; rw [realMultiplierOperator_neg, LinearMap.neg_comp]

theorem sum_rTerm_neg (cs : List (RS N × List (Fin N))) :
    ((cs.map fun c => (-c.1, c.2)).map fun c => rTerm c.1 c.2).sum =
      -((cs.map fun c => rTerm c.1 c.2).sum) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, neg_add, rTerm_neg] at *
    rw [ih]

theorem IsRealDiffOp.neg {k : ℕ} {P : Operator N} (h : IsRealDiffOp k P) : IsRealDiffOp k (-P) := by
  obtain ⟨cs, hcs, rfl⟩ := h
  refine ⟨cs.map fun c => (-c.1, c.2), ?_, (sum_rTerm_neg cs).symm⟩
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hcs d hd

theorem IsRealDiffOp.sub {k : ℕ} {P Q : Operator N} (hP : IsRealDiffOp k P) (hQ : IsRealDiffOp k Q) :
    IsRealDiffOp k (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

/-- Right composition with a coordinate derivative raises the order by one. -/
theorem IsRealDiffOp.rightDeriv {k : ℕ} {P : Operator N} (h : IsRealDiffOp k P) (i : Fin N) :
    IsRealDiffOp (k + 1) (P.comp (coordinateDerivative i)) := by
  obtain ⟨cs, hcs, rfl⟩ := h
  refine ⟨cs.map fun c => (c.1, i :: c.2), ?_, ?_⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    simpa using hcs d hd
  · induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons, LinearMap.add_comp] at *
      rw [← ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))]
      unfold Hormander.B.rTerm
      simp [derivWord, LinearMap.comp_assoc]

theorem coordinateDerivative_comp_realMultiplier (i : Fin N) (c : RS N) :
    (coordinateDerivative i).comp (realMultiplierOperator c) =
      (realMultiplierOperator c).comp (coordinateDerivative i) +
        realMultiplierOperator (rder i c) := by
  have h := operatorComm_coordinateDerivative_realMultiplier i c
  unfold operatorComm at h
  rw [← h]
  abel

/-- A derivative word followed by a multiplier is a differential operator of the same order. -/
theorem isRealDiffOp_derivWord_comp_mult (w : List (Fin N)) :
    ∀ c : RS N, IsRealDiffOp (w.length + 1) ((derivWord w).comp (realMultiplierOperator c)) := by
  induction w with
  | nil =>
    intro c
    have : (derivWord ([] : List (Fin N))).comp (realMultiplierOperator c) = Hormander.B.rTerm c [] := by
      simp [derivWord, Hormander.B.rTerm]
    rw [this]
    exact IsRealDiffOp.of_rTerm c (by simp)
  | cons i w ih =>
    intro c
    have e : (derivWord (i :: w)).comp (realMultiplierOperator c) =
        ((derivWord w).comp (realMultiplierOperator c)).comp (coordinateDerivative i) +
          (derivWord w).comp (realMultiplierOperator (rder i c)) := by
      simp only [derivWord]
      rw [LinearMap.comp_assoc, coordinateDerivative_comp_realMultiplier, LinearMap.comp_add,
        LinearMap.comp_assoc]
    rw [e]
    exact ((ih c).rightDeriv i).add ((ih (rder i c)).mono (by simp))

theorem operatorComm_realMultiplier_coordinateDerivative (g : RS N) (i : Fin N) :
    operatorComm (realMultiplierOperator g) (coordinateDerivative i) =
      -realMultiplierOperator (rder i g) := by
  have h := operatorComm_coordinateDerivative_realMultiplier i g
  unfold operatorComm at h ⊢
  rw [← h]
  abel

/-- A multiplier commutator lowers the order of a derivative word. -/
theorem isRealDiffOp_comm_mult_derivWord (g : RS N) :
    ∀ w : List (Fin N), IsRealDiffOp w.length (operatorComm (realMultiplierOperator g) (derivWord w)) := by
  intro w
  induction w with
  | nil =>
    have : operatorComm (realMultiplierOperator g) (derivWord ([] : List (Fin N))) = 0 := by
      simp [derivWord, operatorComm]
    rw [this]; exact IsRealDiffOp.zero _
  | cons i w ih =>
    have e : operatorComm (realMultiplierOperator g) (derivWord (i :: w)) =
        (operatorComm (realMultiplierOperator g) (derivWord w)).comp (coordinateDerivative i) -
          (derivWord w).comp (realMultiplierOperator (rder i g)) := by
      simp only [derivWord]
      rw [operatorComm_comp_right, operatorComm_realMultiplier_coordinateDerivative,
        LinearMap.comp_neg]
      abel
    rw [e]
    exact (ih.rightDeriv i).sub (by simpa using isRealDiffOp_derivWord_comp_mult w (rder i g))

theorem IsRealDiffOp.sum {k : ℕ} {ι : Type*} (I : Finset ι) (P : ι → Operator N)
    (h : ∀ i ∈ I, IsRealDiffOp k (P i)) : IsRealDiffOp k (∑ i ∈ I, P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsRealDiffOp.zero k
  | insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i I)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem operatorComm_sum_left {ι : Type*} (I : Finset ι) (T : ι → Operator N) (C : Operator N) :
    operatorComm (∑ i ∈ I, T i) C = ∑ i ∈ I, operatorComm (T i) C := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [operatorComm]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, operatorComm_add_left, ih]

theorem operator_comp_sum {ι : Type*} (I : Finset ι) (A : Operator N) (T : ι → Operator N) :
    A.comp (∑ i ∈ I, T i) = ∑ i ∈ I, A.comp (T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, LinearMap.comp_add, ih]

/-- The action of a real vector field on a real Schwartz function. -/
def vfAct (V : RealSchwartzVectorField N) (a : RS N) : RS N :=
  ∑ j : Fin N, rmul (V j) (rder j a)

theorem complexify_vfAct (V : RealSchwartzVectorField N) (a : RS N) :
    complexifyRealSchwartz (vfAct V a) = vectorFieldOperator V (complexifyRealSchwartz a) := by
  ext x
  simp only [vfAct, vectorFieldOperator, complexifyRealSchwartz_apply, sum_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, rmul_apply, realMultiplierOperator_apply]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have : coordinateDerivative j (complexifyRealSchwartz a) = complexifyRealSchwartz (rder j a) := by
    unfold rder; rw [complexify_lineDeriv]; rfl
  rw [this, complexifyRealSchwartz_apply]

theorem operatorComm_vectorField_realMultiplier (V : RealSchwartzVectorField N) (a : RS N) :
    operatorComm (vectorFieldOperator V) (realMultiplierOperator a) =
      realMultiplierOperator (vfAct V a) := by
  rw [vectorFieldOperator_comm_realMultiplier, ← complexify_vfAct]
  rfl

theorem operatorComm_vectorField_coordinateDerivative (V : RealSchwartzVectorField N) (i : Fin N) :
    operatorComm (vectorFieldOperator V) (coordinateDerivative i) =
      -∑ j : Fin N, (realMultiplierOperator (rder i (V j))).comp (coordinateDerivative j) := by
  unfold vectorFieldOperator
  rw [operatorComm_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [operatorComm_comp_left, operatorComm_coordinateDerivative_coordinateDerivative j i,
    operatorComm_realMultiplier_coordinateDerivative]
  simp

/-- A vector-field commutator does not raise the order of a derivative word. -/
theorem isRealDiffOp_comm_vf_derivWord (V : RealSchwartzVectorField N) :
    ∀ w : List (Fin N), IsRealDiffOp (w.length + 1) (operatorComm (vectorFieldOperator V) (derivWord w)) := by
  intro w
  induction w with
  | nil =>
    have : operatorComm (vectorFieldOperator V) (derivWord ([] : List (Fin N))) = 0 := by
      simp [derivWord, operatorComm]
    rw [this]; exact IsRealDiffOp.zero _
  | cons i w ih =>
    have e : operatorComm (vectorFieldOperator V) (derivWord (i :: w)) =
        (operatorComm (vectorFieldOperator V) (derivWord w)).comp (coordinateDerivative i) -
          ∑ j : Fin N, ((derivWord w).comp (realMultiplierOperator (rder i (V j)))).comp
            (coordinateDerivative j) := by
      simp only [derivWord]
      rw [operatorComm_comp_right, operatorComm_vectorField_coordinateDerivative,
        LinearMap.comp_neg, operator_comp_sum]
      simp only [LinearMap.comp_assoc]
      abel
    rw [e]
    refine (ih.rightDeriv i).sub (IsRealDiffOp.sum _ _ (fun j _ => ?_))
    simpa using (isRealDiffOp_derivWord_comp_mult w (rder i (V j))).rightDeriv j

end Hormander.B
