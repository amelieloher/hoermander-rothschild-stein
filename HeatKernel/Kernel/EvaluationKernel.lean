-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.EvaluationVectors
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Kernels from Riesz evaluation vectors

The inner product of half-time evaluation vectors has a basis-independent series
expansion. Measurability of scalar evaluations makes this kernel jointly measurable.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The symmetric kernel formed from the Riesz vectors at half time. -/
def evaluationKernel (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A) : ℝ :=
  inner ℝ (evaluationVector (L (t / 2)) x) (evaluationVector (L (t / 2)) y)

theorem evaluationKernel_symm (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A) :
    evaluationKernel L t x y = evaluationKernel L t y x := real_inner_comm _ _

/-- A kernel section is evaluation of a half-time Riesz vector. -/
theorem evaluationKernel_eq_evaluation (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A) :
    evaluationKernel L t x y = L (t / 2) y (evaluationVector (L (t / 2)) x) := by
  rw [evaluationKernel_symm]
  exact inner_evaluationVector _ _ _

/-- Parseval's identity gives an absolutely summable scalar evaluation series. -/
theorem hasSum_evaluationKernel {ι : Type*} (b : HilbertBasis ι ℝ H)
    (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A) :
    HasSum (fun i => L (t / 2) x (b i) * L (t / 2) y (b i))
      (evaluationKernel L t x y) := by
  have h := b.hasSum_inner_mul_inner (evaluationVector (L (t / 2)) x)
    (evaluationVector (L (t / 2)) y)
  have heq : (fun i => inner ℝ (evaluationVector (L (t / 2)) x) (b i) *
      inner ℝ (b i) (evaluationVector (L (t / 2)) y)) =
      fun i => L (t / 2) x (b i) * L (t / 2) y (b i) := by
    funext i
    rw [inner_evaluationVector, real_inner_comm (evaluationVector (L (t / 2)) y) (b i),
      inner_evaluationVector]
  rw [heq] at h
  exact h

theorem evaluationKernel_eq_tsum {ι : Type*} (b : HilbertBasis ι ℝ H)
    (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A) :
    evaluationKernel L t x y = ∑' i, L (t / 2) x (b i) * L (t / 2) y (b i) :=
  (hasSum_evaluationKernel b L t x y).tsum_eq.symm

/-- Countably many measurable scalar evaluations suffice for joint kernel measurability. -/
theorem measurable_evaluationKernel_of_basis {ι : Type*} [Countable ι] [MeasurableSpace A]
    (b : HilbertBasis ι ℝ H) (L : ℝ → A → H →L[ℝ] ℝ)
    (hL : ∀ i, Measurable (fun p : ℝ × A => L p.1 p.2 (b i))) :
    Measurable (fun p : ℝ × (A × A) => evaluationKernel L p.1 p.2.1 p.2.2) := by
  simp_rw [evaluationKernel_eq_tsum b]
  apply Measurable.tsum
  intro i
  exact ((hL i).comp ((measurable_fst.div_const 2).prodMk
    (measurable_fst.comp measurable_snd))).mul
    ((hL i).comp ((measurable_fst.div_const 2).prodMk
      (measurable_snd.comp measurable_snd)))

/-- Bounds for evaluation functionals give bounds for the kernel. -/
theorem abs_evaluationKernel_le (L : ℝ → A → H →L[ℝ] ℝ) (t : ℝ) (x y : A)
    {C D : ℝ} (hC : ‖L (t / 2) x‖ ≤ C) (hD : ‖L (t / 2) y‖ ≤ D) :
    |evaluationKernel L t x y| ≤ C * D := by
  calc
    |evaluationKernel L t x y| ≤
        ‖evaluationVector (L (t / 2)) x‖ * ‖evaluationVector (L (t / 2)) y‖ :=
      abs_real_inner_le_norm _ _
    _ = ‖L (t / 2) x‖ * ‖L (t / 2) y‖ := by rw [norm_evaluationVector, norm_evaluationVector]
    _ ≤ C * D := mul_le_mul hC hD (norm_nonneg _) ((norm_nonneg _).trans hC)

end HeatKernel
