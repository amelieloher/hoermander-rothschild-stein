-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.IteratedDerivativeFlattening
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

/-- Derivative remainders follow from finite jets and Taylor integration,
with no differentiation of the pointwise error (BB pp. 412–413). -/
theorem norm_derivative_le_of_vanishing_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {y : E} {n r : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ((n+1+r : ℕ) : WithTop ℕ∞) f (t • y))
    (hzero : ∀ k ≤ n+r, iteratedFDeriv ℝ k f 0 = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (n+1+r) f (t • y)‖ ≤ M) :
    ‖iteratedFDeriv ℝ r f y‖ ≤ M * ‖y‖ ^ (n+1) := by
  apply norm_le_of_vanishing_jets hM
  · intro t ht
    exact (hf t ht).iteratedFDeriv_right (by norm_cast)
  · intro k hk
    apply norm_eq_zero.mp
    rw [norm_iterated_derivative_flattening,hzero (k+r) (by omega),norm_zero]
  · intro t ht
    rw [norm_iterated_derivative_flattening]
    exact hbound t ht
end RothschildStein.G3
