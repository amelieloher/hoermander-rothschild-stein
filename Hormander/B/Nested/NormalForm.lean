-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.RealDiffOps

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.B

variable {N : ℕ}

theorem nestedComm_succ (σ : ℝ) (q : ℕ) (gs : Fin (q + 1) → RS N) :
    nestedComm σ (q + 1) gs =
      operatorComm (realMultiplierOperator (gs 0)) (nestedComm σ q (Fin.tail gs)) := rfl

theorem nestedComm_cons (σ : ℝ) (q : ℕ) (g : RS N) (gs : Fin q → RS N) :
    operatorComm (realMultiplierOperator g) (nestedComm σ q gs) =
      nestedComm σ (q + 1) (Fin.cons g gs) := by
  rw [nestedComm_succ]; simp

theorem operatorComm_sum_right {ι : Type*} (I : Finset ι) (A : Operator N) (T : ι → Operator N) :
    operatorComm A (∑ i ∈ I, T i) = ∑ i ∈ I, operatorComm A (T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [operatorComm]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, operatorComm_add_right, ih]

/-- A coordinate derivative is a derivation of nested multiplier commutators. -/
theorem operatorComm_coordinateDerivative_nestedComm (σ : ℝ) (j : Fin N) :
    ∀ (q : ℕ) (gs : Fin q → RS N),
      operatorComm (coordinateDerivative j) (nestedComm σ q gs) =
        ∑ i : Fin q, nestedComm σ q (Function.update gs i (rder j (gs i))) := by
  intro q
  induction q with
  | zero =>
    intro gs
    simp only [nestedComm, Finset.univ_eq_empty, Finset.sum_empty]
    rw [operatorComm_antisymm, operatorComm_lambda_coordinateDerivative]
    simp
  | succ q ih =>
    intro gs
    rw [nestedComm_succ, operatorComm_jacobi, operatorComm_coordinateDerivative_realMultiplier,
      ih, Fin.sum_univ_succ, operatorComm_sum_right]
    refine congrArg₂ (· + ·) ?_ ?_
    · rw [nestedComm_succ]
      simp
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [nestedComm_succ]
      have h0 : Function.update gs i.succ (rder j (gs i.succ)) 0 = gs 0 :=
        Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
      have ht : Fin.tail (Function.update gs i.succ (rder j (gs i.succ))) =
          Function.update (Fin.tail gs) i (rder j (Fin.tail gs i)) := by
        rw [Fin.tail_update_succ]; rfl
      rw [h0, ht]

/-- The optional left coefficient: `none` is the identity, `some a` is multiplication by `a`. -/
def mulOpt : Option (RS N) → Operator N
  | none => LinearMap.id
  | some a => realMultiplierOperator a

/-- A term `M_a ∘ G ∘ ∂_w` of the normal form, with `G` a `q`-fold nested multiplier
commutator of `Λ^σ`, `|w| + p ≤ q`. -/
def IsNFTerm (σ : ℝ) (p : ℕ) (T : Operator N) : Prop :=
  ∃ (a : Option (RS N)) (q : ℕ) (gs : Fin q → RS N) (w : List (Fin N)), w.length + p ≤ q ∧
    T = (mulOpt a).comp ((nestedComm σ q gs).comp (derivWord w))

/-- Finite sums of normal-form terms. -/
def IsNormalForm (σ : ℝ) (p : ℕ) (T : Operator N) : Prop :=
  ∃ ts : List (Operator N), (∀ t ∈ ts, IsNFTerm σ p t) ∧ T = ts.sum

theorem IsNormalForm.zero (σ : ℝ) (p : ℕ) : IsNormalForm σ p (0 : Operator N) := ⟨[], by simp, by simp⟩

theorem IsNFTerm.isNormalForm {σ : ℝ} {p : ℕ} {T : Operator N} (h : IsNFTerm σ p T) :
    IsNormalForm σ p T := ⟨[T], by simpa using h, by simp⟩

theorem IsNormalForm.add {σ : ℝ} {p : ℕ} {S T : Operator N} (hS : IsNormalForm σ p S)
    (hT : IsNormalForm σ p T) : IsNormalForm σ p (S + T) := by
  obtain ⟨ss, hs, rfl⟩ := hS
  obtain ⟨ts, ht, rfl⟩ := hT
  refine ⟨ss ++ ts, ?_, by simp [List.sum_append]⟩
  intro t h
  rcases List.mem_append.mp h with h | h
  exacts [hs t h, ht t h]

theorem IsNormalForm.finsetSum {σ : ℝ} {p : ℕ} {ι : Type*} (I : Finset ι) (T : ι → Operator N)
    (h : ∀ i ∈ I, IsNormalForm σ p (T i)) : IsNormalForm σ p (∑ i ∈ I, T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsNormalForm.zero σ p
  | insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i I)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem IsNormalForm.listSum {σ : ℝ} {p : ℕ} (ts : List (Operator N))
    (h : ∀ t ∈ ts, IsNormalForm σ p t) : IsNormalForm σ p ts.sum := by
  induction ts with
  | nil => simpa using IsNormalForm.zero σ p
  | cons t ts ih =>
    rw [List.sum_cons]
    exact (h t (by simp)).add (ih (fun s hs => h s (by simp [hs])))

/-- Multiplying the optional coefficient by a real Schwartz function. -/
def mulCoeff (a : Option (RS N)) (c : RS N) : RS N :=
  match a with
  | none => c
  | some a => rmul a c

theorem mulOpt_comp_real (a : Option (RS N)) (c : RS N) :
    (mulOpt a).comp (realMultiplierOperator c) = mulOpt (some (mulCoeff a c)) := by
  cases a with
  | none => rfl
  | some a => simp [mulOpt, mulCoeff, realMultiplierOperator_rmul]

theorem nestedComm_comp_realMultiplier (σ : ℝ) (q : ℕ) (gs : Fin q → RS N) (c : RS N) :
    (nestedComm σ q gs).comp (realMultiplierOperator c) =
      (realMultiplierOperator c).comp (nestedComm σ q gs) +
        nestedComm σ (q + 1) (Fin.cons (-c) gs) := by
  have : nestedComm σ (q + 1) (Fin.cons (-c) gs) =
      (nestedComm σ q gs).comp (realMultiplierOperator c) -
        (realMultiplierOperator c).comp (nestedComm σ q gs) := by
    rw [← nestedComm_cons, realMultiplierOperator_neg]
    unfold operatorComm
    rw [LinearMap.neg_comp, LinearMap.comp_neg]
    abel
  rw [this]
  abel

theorem isNormalForm_mul_nested_rTerm (σ : ℝ) {p q : ℕ} (a : Option (RS N)) (gs : Fin q → RS N)
    (c : RS N) {w : List (Fin N)} (hw : w.length + p ≤ q) :
    IsNormalForm σ p
      ((mulOpt a).comp ((nestedComm σ q gs).comp (rTerm c w))) := by
  have e : (mulOpt a).comp ((nestedComm σ q gs).comp (rTerm c w)) =
      (mulOpt (some (mulCoeff a c))).comp ((nestedComm σ q gs).comp (derivWord w)) +
        (mulOpt a).comp ((nestedComm σ (q + 1) (Fin.cons (-c) gs)).comp (derivWord w)) := by
    unfold rTerm
    have h1 := nestedComm_comp_realMultiplier σ q gs c
    have h2 := mulOpt_comp_real a c
    have hshape : (mulOpt a).comp ((nestedComm σ q gs).comp ((realMultiplierOperator c).comp (derivWord w))) =
        (mulOpt a).comp (((nestedComm σ q gs).comp (realMultiplierOperator c)).comp (derivWord w)) := by
      simp only [LinearMap.comp_assoc]
    rw [hshape, h1, LinearMap.add_comp, LinearMap.comp_add, ← h2]
    simp only [LinearMap.comp_assoc]
  rw [e]
  refine IsNormalForm.add (IsNFTerm.isNormalForm ?_) (IsNFTerm.isNormalForm ?_)
  · exact ⟨some (mulCoeff a c), q, gs, w, hw, rfl⟩
  · exact ⟨a, q + 1, Fin.cons (-c) gs, w, by omega, rfl⟩

theorem isNormalForm_mul_nested_rdo (σ : ℝ) {p q b : ℕ} (a : Option (RS N)) (gs : Fin q → RS N)
    (hb : b + p ≤ q + 1) {Q : Operator N} (hQ : IsRealDiffOp b Q) :
    IsNormalForm σ p ((mulOpt a).comp ((nestedComm σ q gs).comp Q)) := by
  obtain ⟨cs, hcs, rfl⟩ := hQ
  induction cs with
  | nil => simpa using IsNormalForm.zero σ p
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, LinearMap.comp_add]
    refine IsNormalForm.add ?_ (ih (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')))
    have := hcs c List.mem_cons_self
    exact isNormalForm_mul_nested_rTerm σ a gs c.1 (by omega)

theorem operatorComm_realMultiplier_mulOpt (g : RS N) (a : Option (RS N)) :
    operatorComm (realMultiplierOperator g) (mulOpt a) = 0 := by
  cases a with
  | none => simp [mulOpt, operatorComm]
  | some a => exact operatorComm_realMultiplier_realMultiplier g a

theorem derivWord_snoc (j : Fin N) (w : List (Fin N)) :
    (coordinateDerivative j).comp (derivWord w) = derivWord (w ++ [j]) := by
  induction w with
  | nil => simp [derivWord]
  | cons i w ih =>
    simp only [List.cons_append, derivWord]
    rw [← ih, LinearMap.comp_assoc]

/-- A multiplier commutator of a normal-form term is a normal form with one more multiplier. -/
theorem isNormalForm_comm_mult (σ : ℝ) {p : ℕ} {T : Operator N} (hT : IsNFTerm σ p T) (g : RS N) :
    IsNormalForm σ (p + 1) (operatorComm (realMultiplierOperator g) T) := by
  obtain ⟨a, q, gs, w, hw, rfl⟩ := hT
  have e : operatorComm (realMultiplierOperator g)
      ((mulOpt a).comp ((nestedComm σ q gs).comp (derivWord w))) =
      (mulOpt a).comp ((nestedComm σ (q + 1) (Fin.cons g gs)).comp (derivWord w)) +
        (mulOpt a).comp ((nestedComm σ q gs).comp
          (operatorComm (realMultiplierOperator g) (derivWord w))) := by
    rw [operatorComm_comp_right, operatorComm_realMultiplier_mulOpt, LinearMap.zero_comp, zero_add,
      operatorComm_comp_right, nestedComm_cons]
    simp only [LinearMap.comp_add]
  rw [e]
  refine IsNormalForm.add (IsNFTerm.isNormalForm ⟨a, q + 1, Fin.cons g gs, w, by omega, rfl⟩) ?_
  exact isNormalForm_mul_nested_rdo σ a gs (b := w.length) (by omega)
    (isRealDiffOp_comm_mult_derivWord g w)

theorem operator_sum_comp {ι : Type*} (I : Finset ι) (T : ι → Operator N) (B : Operator N) :
    (∑ i ∈ I, T i).comp B = ∑ i ∈ I, (T i).comp B := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, LinearMap.add_comp, ih]

theorem operatorComm_vectorField_nestedComm (σ : ℝ) (V : RealSchwartzVectorField N) (q : ℕ)
    (gs : Fin q → RS N) :
    operatorComm (vectorFieldOperator V) (nestedComm σ q gs) =
      ∑ j : Fin N, ((realMultiplierOperator (V j)).comp
          (∑ i : Fin q, nestedComm σ q (Function.update gs i (rder j (gs i)))) +
        (nestedComm σ (q + 1) (Fin.cons (V j) gs)).comp (coordinateDerivative j)) := by
  unfold vectorFieldOperator
  rw [operatorComm_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [operatorComm_comp_left, operatorComm_coordinateDerivative_nestedComm, nestedComm_cons]

/-- A vector-field commutator of a normal-form term is a normal form with the same multiplier
count. -/
theorem isNormalForm_comm_vf (σ : ℝ) {p : ℕ} {T : Operator N} (hT : IsNFTerm σ p T)
    (V : RealSchwartzVectorField N) :
    IsNormalForm σ p (operatorComm (vectorFieldOperator V) T) := by
  obtain ⟨a, q, gs, w, hw, rfl⟩ := hT
  have e : operatorComm (vectorFieldOperator V)
      ((mulOpt a).comp ((nestedComm σ q gs).comp (derivWord w))) =
      (operatorComm (vectorFieldOperator V) (mulOpt a)).comp
          ((nestedComm σ q gs).comp (derivWord w)) +
        ((mulOpt a).comp (((operatorComm (vectorFieldOperator V) (nestedComm σ q gs)).comp
            (derivWord w))) +
          (mulOpt a).comp ((nestedComm σ q gs).comp
            (operatorComm (vectorFieldOperator V) (derivWord w)))) := by
    rw [operatorComm_comp_right, operatorComm_comp_right, LinearMap.comp_add]
  rw [e]
  refine IsNormalForm.add ?_ (IsNormalForm.add ?_ ?_)
  · -- the coefficient term
    cases a with
    | none =>
      have : operatorComm (vectorFieldOperator V) (mulOpt (none : Option (RS N))) = 0 := by
        simp [mulOpt, operatorComm]
      rw [this, LinearMap.zero_comp]
      exact IsNormalForm.zero σ p
    | some a =>
      have : operatorComm (vectorFieldOperator V) (mulOpt (some a)) =
          realMultiplierOperator (vfAct V a) := operatorComm_vectorField_realMultiplier V a
      rw [this]
      exact IsNFTerm.isNormalForm ⟨some (vfAct V a), q, gs, w, hw, rfl⟩
  · -- the term from the nested commutator
    rw [operatorComm_vectorField_nestedComm, operator_sum_comp, operator_comp_sum]
    refine IsNormalForm.finsetSum _ _ (fun j _ => ?_)
    have e2 : (mulOpt a).comp
        ((((realMultiplierOperator (V j)).comp
          (∑ i : Fin q, nestedComm σ q (Function.update gs i (rder j (gs i)))) +
          (nestedComm σ (q + 1) (Fin.cons (V j) gs)).comp (coordinateDerivative j))).comp
            (derivWord w)) =
        ∑ i : Fin q, (mulOpt (some (mulCoeff a (V j)))).comp
            ((nestedComm σ q (Function.update gs i (rder j (gs i)))).comp (derivWord w)) +
          (mulOpt a).comp ((nestedComm σ (q + 1) (Fin.cons (V j) gs)).comp
            (derivWord (w ++ [j]))) := by
      rw [LinearMap.add_comp, LinearMap.comp_add, operator_comp_sum, operator_sum_comp,
        operator_comp_sum, ← derivWord_snoc]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← mulOpt_comp_real]
        simp only [LinearMap.comp_assoc]
      · simp only [LinearMap.comp_assoc]
    rw [e2]
    refine IsNormalForm.add (IsNormalForm.finsetSum _ _ (fun i _ => IsNFTerm.isNormalForm ?_))
      (IsNFTerm.isNormalForm ?_)
    · exact ⟨some (mulCoeff a (V j)), q, _, w, hw, rfl⟩
    · exact ⟨a, q + 1, Fin.cons (V j) gs, w ++ [j], by simp; omega, rfl⟩
  · exact isNormalForm_mul_nested_rdo σ a gs (b := w.length + 1) (by omega)
      (isRealDiffOp_comm_vf_derivWord V w)

theorem operatorComm_list_sum_right (Y : Operator N) (ts : List (Operator N)) :
    operatorComm Y ts.sum = (ts.map (operatorComm Y)).sum := by
  induction ts with
  | nil => simp [operatorComm]
  | cons t ts ih => rw [List.sum_cons, operatorComm_add_right, ih, List.map_cons, List.sum_cons]

theorem multiplierCount_cons_multiplier (g : RS N) (ys : List (OperatorGenerator N)) :
    multiplierCount (OperatorGenerator.multiplier g :: ys) = multiplierCount ys + 1 := by
  unfold multiplierCount
  rw [List.filter_cons]
  simp [OperatorGenerator.isMultiplier]

theorem multiplierCount_cons_vectorField (V : RealSchwartzVectorField N) (ys : List (OperatorGenerator N)) :
    multiplierCount (OperatorGenerator.vectorField V :: ys) = multiplierCount ys := by
  unfold multiplierCount
  rw [List.filter_cons]
  simp [OperatorGenerator.isMultiplier]

/-- Normal form for interleaved commutators: for any finite sequence of real Schwartz
vector fields and real Schwartz multipliers with `p` multiplier entries, the iterated commutator
`ad_{Y₁}⋯ad_{Y_r} Λ^σ` is a finite sum of terms `M_a G ∂_w` with `a` real Schwartz or `1`,
`G` a `q`-fold nested multiplier commutator of `Λ^σ`, and `|w| + p ≤ q`. -/
theorem normal_form (σ : ℝ) (ys : List (OperatorGenerator N)) :
    IsNormalForm σ (multiplierCount ys) (iteratedCommutator ys (lambdaOperator σ)) := by
  induction ys with
  | nil =>
    refine IsNFTerm.isNormalForm ⟨none, 0, fun i => i.elim0, [], by simp [multiplierCount], ?_⟩
    simp [iteratedCommutator, nestedComm, mulOpt, derivWord]
  | cons Y ys ih =>
    obtain ⟨ts, hts, hT⟩ := ih
    have e : iteratedCommutator (Y :: ys) (lambdaOperator σ) =
        (ts.map (operatorComm Y.toOperator)).sum := by
      rw [iteratedCommutator, hT, operatorComm_list_sum_right]
    rw [e]
    cases Y with
    | multiplier g =>
      rw [multiplierCount_cons_multiplier]
      refine IsNormalForm.listSum _ (fun t ht => ?_)
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact isNormalForm_comm_mult σ (hts t' ht') g
    | vectorField V =>
      rw [multiplierCount_cons_vectorField]
      refine IsNormalForm.listSum _ (fun t ht => ?_)
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact isNormalForm_comm_vf σ (hts t' ht') V

theorem hasOrder_derivWord : ∀ w : List (Fin N), HasOrder (w.length : ℝ) (derivWord w)
  | [] => by simpa [derivWord, lambdaOperator_zero] using hasOrder_lambdaOperator (N := N) (0 : ℝ)
  | i :: w => by
    have := (hasOrder_derivWord w).comp (hasOrder_coordinateDerivative i)
    simpa [derivWord, add_comm] using this

theorem hasOrder_mulOpt (a : Option (RS N)) : HasOrder 0 (mulOpt a) := by
  cases a with
  | none => simpa [mulOpt, lambdaOperator_zero] using hasOrder_lambdaOperator (N := N) (0 : ℝ)
  | some a => exact hasOrder_multiplierOperator_zero (complexifyRealSchwartz a)

/-- Each normal-form term with `p` multipliers has order `σ - p`. -/
theorem IsNFTerm.hasOrder {σ : ℝ} {p : ℕ} {T : Operator N} (h : IsNFTerm σ p T) :
    HasOrder (σ - p) T := by
  obtain ⟨a, q, gs, w, hw, rfl⟩ := h
  have h1 := (hasOrder_mulOpt a).comp ((hasOrder_nestedComm σ q gs).comp (hasOrder_derivWord w))
  refine h1.mono ?_
  have : (w.length : ℝ) + p ≤ q := by exact_mod_cast hw
  linarith

theorem IsNormalForm.hasOrder {σ : ℝ} {p : ℕ} {T : Operator N} (h : IsNormalForm σ p T) :
    HasOrder (σ - p) T := by
  obtain ⟨ts, hts, rfl⟩ := h
  induction ts with
  | nil => simpa using hasOrder_zero (σ - p)
  | cons t ts ih =>
    rw [List.sum_cons]
    exact (hts t List.mem_cons_self).hasOrder.add (ih (fun s hs => hts s (List.mem_cons_of_mem _ hs)))

/-- Every iterated commutator of `Λ^σ` with real Schwartz vector fields and multipliers has
order `σ - (number of multiplier entries)`. -/
theorem iteratedCommutator_lambda_order (σ : ℝ) (ys : List (OperatorGenerator N)) :
    HasOrder (σ - (multiplierCount ys : ℝ)) (iteratedCommutator ys (lambdaOperator σ)) :=
  (normal_form σ ys).hasOrder

end Hormander.B
