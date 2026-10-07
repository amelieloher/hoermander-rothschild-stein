-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Calculus.OrderClassAlgebra

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- All assignments of a commutator word to the two factors of a product. -/
def commutatorWordSplits : List (OperatorGenerator N) →
    List (List (OperatorGenerator N) × List (OperatorGenerator N))
  | [] => [([], [])]
  | Y :: ys => (commutatorWordSplits ys).flatMap fun p =>
      [(Y :: p.1, p.2), (p.1, Y :: p.2)]

theorem multiplierCount_cons_local (Y : OperatorGenerator N)
    (ys : List (OperatorGenerator N)) :
    multiplierCount (Y :: ys) =
      (if Y.isMultiplier then 1 else 0) + multiplierCount ys := by
  cases Y with
  | vectorField V => simp [multiplierCount, List.filter, OperatorGenerator.isMultiplier]
  | multiplier g =>
      simp [multiplierCount, List.filter, OperatorGenerator.isMultiplier]
      omega

theorem multiplierCount_split_local (ys : List (OperatorGenerator N))
    (p : List (OperatorGenerator N) × List (OperatorGenerator N))
    (hp : p ∈ commutatorWordSplits ys) :
    multiplierCount p.1 + multiplierCount p.2 = multiplierCount ys := by
  induction ys generalizing p with
  | nil =>
      simp [commutatorWordSplits] at hp
      rcases hp with rfl
      simp [multiplierCount]
  | cons Y ys ih =>
      simp only [commutatorWordSplits, List.mem_flatMap] at hp
      rcases hp with ⟨q, hq, hp⟩
      rcases q with ⟨l, r⟩
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp | hp
      · cases hp
        change multiplierCount (Y :: l) + multiplierCount r =
          multiplierCount (Y :: ys)
        rw [multiplierCount_cons_local, multiplierCount_cons_local]
        have hcounts := ih (l, r) hq
        calc
          _ = (if Y.isMultiplier then 1 else 0) +
              (multiplierCount l + multiplierCount r) := by omega
          _ = _ := by rw [hcounts]
      · cases hp
        change multiplierCount l + multiplierCount (Y :: r) =
          multiplierCount (Y :: ys)
        rw [multiplierCount_cons_local, multiplierCount_cons_local]
        have hcounts := ih (l, r) hq
        calc
          _ = (if Y.isMultiplier then 1 else 0) +
              (multiplierCount l + multiplierCount r) := by omega
          _ = _ := by rw [hcounts]
      · simp at hp

theorem operatorComm_comp_listSum_local (P : Operator N)
    (ts : List (Operator N × Operator N)) :
    operatorComm P ((ts.map fun p => p.1.comp p.2).sum) =
      (ts.flatMap fun p =>
        [((operatorComm P p.1).comp p.2), p.1.comp (operatorComm P p.2)]).sum := by
  induction ts with
  | nil => simp [operatorComm]
  | cons p ts ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.sum_append,
        operatorComm_add_right_local, operatorComm_comp, ih]
      simp only [List.sum_nil]
      abel_nf

/-- The iterated commutator of a product is the sum over all assignments of
commutators to its two factors. -/
theorem iteratedCommutator_comp_expansion (ys : List (OperatorGenerator N))
    (A B : Operator N) :
    iteratedCommutator ys (A.comp B) =
      ((commutatorWordSplits ys).map fun p =>
        (iteratedCommutator p.1 A).comp (iteratedCommutator p.2 B)).sum := by
  induction ys with
  | nil => simp [commutatorWordSplits, iteratedCommutator]
  | cons Y ys ih =>
      change operatorComm Y.toOperator (iteratedCommutator ys (A.comp B)) = _
      rw [ih]
      let tsOps := (commutatorWordSplits ys).map fun p =>
        (iteratedCommutator p.1 A, iteratedCommutator p.2 B)
      have h := operatorComm_comp_listSum_local Y.toOperator tsOps
      have hmap :
          (commutatorWordSplits ys).map (fun p =>
            (iteratedCommutator p.1 A).comp (iteratedCommutator p.2 B)) =
          tsOps.map (fun p => p.1.comp p.2) := by
        simp [tsOps, List.map_map]
      rw [hmap]
      rw [h]
      have hflat :
          tsOps.flatMap (fun p =>
            [((operatorComm Y.toOperator p.1).comp p.2),
              p.1.comp (operatorComm Y.toOperator p.2)]) =
          (commutatorWordSplits ys).flatMap (fun p =>
            [((iteratedCommutator (Y :: p.1) A).comp
                (iteratedCommutator p.2 B)),
              ((iteratedCommutator p.1 A).comp
                (iteratedCommutator (Y :: p.2) B))]) := by
        simp [tsOps, List.flatMap_map,
          iteratedCommutator]
      rw [hflat]
      simp [commutatorWordSplits, List.map_flatMap, iteratedCommutator]

theorem hasOrder_listSum_local {α : Type*} (ts : List α) (f : α → Operator N) (m : ℝ)
    (h : ∀ t ∈ ts, HasOrder m (f t)) : HasOrder m ((ts.map f).sum) := by
  induction ts with
  | nil => simpa using hasOrder_zero (N := N) m
  | cons t ts ih =>
      rw [List.map_cons, List.sum_cons]
      exact (h t (by simp)).add (ih fun t' ht' => h t' (by simp [ht']))

/-- Product commutator words inherit the sum of the two class orders. -/
theorem iteratedCommutator_comp_order {m n : ℝ} {A B : Operator N}
    (hA : OperatorClass m A) (hB : OperatorClass n B)
    (ys : List (OperatorGenerator N)) :
    HasOrder (m + n - (multiplierCount ys : ℝ))
      (iteratedCommutator ys (A.comp B)) := by
  rw [iteratedCommutator_comp_expansion]
  apply hasOrder_listSum_local
  intro p hp
  have hc := multiplierCount_split_local ys p hp
  have hidx :
      (m - (multiplierCount p.1 : ℝ)) +
        (n - (multiplierCount p.2 : ℝ)) =
      m + n - (multiplierCount ys : ℝ) := by
    have hcast : (multiplierCount p.1 : ℝ) +
        (multiplierCount p.2 : ℝ) = (multiplierCount ys : ℝ) := by
      exact_mod_cast hc
    linarith
  have hterm := (hA.iterated_order p.1).comp (hB.iterated_order p.2)
  rw [hidx] at hterm
  exact hterm

/-- Composition adds the orders of commutator-stable operators. -/
theorem OperatorClass.comp {m n : ℝ} {A B : Operator N}
    (hA : OperatorClass m A) (hB : OperatorClass n B) :
    OperatorClass (m + n) (A.comp B) := by
  rcases hA with ⟨At, hAt, hAorders⟩
  rcases hB with ⟨Bt, hBt, hBorders⟩
  refine ⟨Bt.comp At, bilinearTranspose_comp hAt hBt, ?_⟩
  intro ys
  exact iteratedCommutator_comp_order
    ⟨At, hAt, hAorders⟩ ⟨Bt, hBt, hBorders⟩ ys

end Hormander.B
