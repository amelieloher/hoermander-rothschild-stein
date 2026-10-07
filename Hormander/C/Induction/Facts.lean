-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Energy.Estimate

@[expose] public section

noncomputable section

namespace Hormander.C

open Hormander.B

/-- The closure facts used by the energy and word estimates, stated verbatim with the shared
`OperatorClass`: (i) generators, (ii) vector space / composition / monotonicity, (iii) commutator
stability, (iv) transposes. The conditional helpers of this section take it as a hypothesis, to be
instantiated when the operator estimates are established. -/
structure B10Facts (N : ℕ) : Prop where
  lambda_mem : ∀ σ : ℝ, OperatorClass σ (lambdaOperator (N := N) σ)
  multiplier_mem : ∀ g : SchwartzMap (Carrier N) ℝ, OperatorClass 0 (realMultiplierOperator g)
  vectorField_mem : ∀ X : RealSchwartzVectorField N, OperatorClass 1 (vectorFieldOperator X)
  zero_mem : ∀ m : ℝ, OperatorClass m (0 : Operator N)
  add_mem : ∀ (m : ℝ) (A B : Operator N), OperatorClass m A → OperatorClass m B →
    OperatorClass m (A + B)
  smul_mem : ∀ (m : ℝ) (c : ℂ) (A : Operator N), OperatorClass m A → OperatorClass m (c • A)
  mono_mem : ∀ (m m' : ℝ) (A : Operator N), OperatorClass m A → m ≤ m' → OperatorClass m' A
  comp_mem : ∀ (a b : ℝ) (T U : Operator N), OperatorClass a T → OperatorClass b U →
    OperatorClass (a + b) (T.comp U)
  comm_vectorField : ∀ (m : ℝ) (T : Operator N) (X : RealSchwartzVectorField N),
    OperatorClass m T → OperatorClass m (operatorComm (vectorFieldOperator X) T)
  comm_multiplier : ∀ (m : ℝ) (T : Operator N) (g : SchwartzMap (Carrier N) ℝ),
    OperatorClass m T → OperatorClass (m - 1) (operatorComm (realMultiplierOperator g) T)
  transpose_mem : ∀ (m : ℝ) (T Tt : Operator N), OperatorClass m T → HasBilinearTranspose T Tt →
    OperatorClass m Tt

theorem _root_.Hormander.B.OperatorClass.hasOrder' {N : ℕ} {m : ℝ} {T : Operator N} (h : OperatorClass m T) :
    HasOrder m T := by
  obtain ⟨Tt, _, hord⟩ := h
  simpa [iteratedCommutator, multiplierCount] using hord []

theorem B10Facts.sum_mem {N : ℕ} (F : B10Facts N) {ι : Type*} (I : Finset ι)
    (T : ι → Operator N) (m : ℝ) (h : ∀ i ∈ I, OperatorClass m (T i)) :
    OperatorClass m (∑ i ∈ I, T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using F.zero_mem m
  | insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact F.add_mem m _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Hormander.C
