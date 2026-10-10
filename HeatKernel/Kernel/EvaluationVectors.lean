-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.LocalEvaluation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Riesz vectors for bounded evaluations

Bounded linear evaluations on a real Hilbert space have unique Riesz vectors.
Evaluation identities for a self-adjoint semigroup transfer to these vectors.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Riesz vector of a bounded linear evaluation. -/
def evaluationVector (L : A → H →L[ℝ] ℝ) (a : A) : H :=
  (InnerProductSpace.toDual ℝ H).symm (L a)

@[simp] theorem inner_evaluationVector (L : A → H →L[ℝ] ℝ) (a : A) (f : H) :
    inner ℝ (evaluationVector L a) f = L a f :=
  InnerProductSpace.toDual_symm_apply

@[simp] theorem norm_evaluationVector (L : A → H →L[ℝ] ℝ) (a : A) :
    ‖evaluationVector L a‖ = ‖L a‖ := (InnerProductSpace.toDual ℝ H).symm.norm_map _

/-- An evaluation composition law transfers to Riesz vectors under self-adjointness. -/
theorem evaluationVector_add_of_selfAdjoint (L : ℝ → A → H →L[ℝ] ℝ)
    (T : ℝ → H →L[ℝ] H) {s t : ℝ} (hT : IsSelfAdjoint (T s))
    (hlaw : ∀ x f, L (t + s) x f = L t x (T s f)) (x : A) :
    evaluationVector (L (t + s)) x = T s (evaluationVector (L t) x) := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationVector, hlaw]
  exact (inner_evaluationVector (L t) x (T s f)).symm.trans (hT.isSymmetric _ _).symm

end HeatKernel
