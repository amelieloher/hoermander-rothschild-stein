-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords
public import RothschildStein.Definitions.sumSquaresWithDrift
public import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3

/-- far part. A field derivative passes through the actual
finite drift sum-of-squares on a smooth input. Differentiability of
all summands is proved from the shared word-smoothness theorem. -/
theorem fieldDerivative_sumSquaresWithDrift {N q : ℕ}
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Fin N → ℝ) :
    fieldDerivative V (sumSquaresWithDrift Y f) x =
      fieldDerivative V (fieldDerivative (Y 0) f) x +
        ∑ i : Fin q, fieldDerivative V
          (fieldDerivative (Y i.succ) (fieldDerivative (Y i.succ) f)) x := by
  have hw (I : List (Fin (q + 1))) : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative Y I f) :=
    contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Y (fun i => (hY i).contDiffOn)
      I f hf.contDiffOn)
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (Y 0) f) := hw [0]
  have h2 (i : Fin q) : ContDiff ℝ (⊤ : ℕ∞)
      (fieldDerivative (Y i.succ) (fieldDerivative (Y i.succ) f)) := hw [i.succ, i.succ]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ i : Fin q,
      fieldDerivative (Y i.succ) (fieldDerivative (Y i.succ) f) y) :=
    ContDiff.sum (fun i _ => h2 i)
  change fderiv ℝ (fun y => fieldDerivative (Y 0) f y +
      ∑ i : Fin q, fieldDerivative (Y i.succ) (fieldDerivative (Y i.succ) f) y) x (V x) = _
  rw [fderiv_fun_add (h0.differentiable (by simp)).differentiableAt
      (hs.differentiable (by simp)).differentiableAt,
    fderiv_fun_sum (fun i _ => ((h2 i).differentiable (by simp)).differentiableAt)]
  simp only [add_apply, sum_apply]
  rfl

end RothschildStein.H3
