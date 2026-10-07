-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DerivativeFlatRemainder
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G3

/-- Finite smoothness and matching jets give an actual pointwise Taylor error. -/
theorem norm_point_error_of_finite_matching_jets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f g : E → F) (s : ℕ) (y : E) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((s+1 : ℕ) : WithTop ℕ∞) f (t • y))
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((s+1 : ℕ) : WithTop ℕ∞) g (t • y))
    (hmatch : ∀ k ≤ s, iteratedFDeriv ℝ k f 0 = iteratedFDeriv ℝ k g 0)
    (hfjet : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (s+1) f (t • y)‖ ≤ A)
    (hgjet : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (s+1) g (t • y)‖ ≤ B) :
    ‖f y-g y‖ ≤ (A+B)*‖y‖^(s+1) := by
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hflat : ∀ k ≤ s, iteratedFDeriv ℝ k (f-g) 0 = 0 := by
    intro k hk
    have hfs : ContDiffAt ℝ k f 0 := by
      simpa only [zero_smul] using (hf 0 hz).of_le (by exact_mod_cast (show k ≤ s+1 by omega))
    have hgs : ContDiffAt ℝ k g 0 := by
      simpa only [zero_smul] using (hg 0 hz).of_le (by exact_mod_cast (show k ≤ s+1 by omega))
    rw [iteratedFDeriv_sub_apply hfs hgs,hmatch k hk,sub_self]
  have he := norm_derivative_le_of_vanishing_jets (f := f-g) (n := s) (r := 0)
    (y := y) (add_nonneg hA hB)
    (fun t ht => by simpa only [Nat.add_zero,Pi.sub_def] using (hf t ht).sub (hg t ht))
    (by simpa only [Nat.add_zero] using hflat)
    (fun t ht => by
      simp only [Nat.add_zero]
      rw [iteratedFDeriv_sub_apply (hf t ht) (hg t ht)]
      exact (norm_sub_le _ _).trans (add_le_add (hfjet t ht) (hgjet t ht)))
  simpa only [norm_iteratedFDeriv_zero,Pi.sub_apply] using he
end RothschildStein.G3
