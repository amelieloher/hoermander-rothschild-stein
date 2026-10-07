-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteSmoothSymmetry
public import Mathlib.Analysis.Analytic.IteratedFDeriv

@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem symmetric_multilinear_eq_of_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (A B : E [×n]→L[ℝ] F)
    (hA : ∀ (σ : Equiv.Perm (Fin n)) u, A (fun j => u (σ j)) = A u)
    (hB : ∀ (σ : Equiv.Perm (Fin n)) u, B (fun j => u (σ j)) = B u)
    (hd : ∀ v, A (fun _ => v) = B (fun _ => v)) : A = B := by
  have he : (fun v : E => A (fun _ => v)) = (fun v => B (fun _ => v)) := funext hd
  ext u
  have hj := congrArg (fun f : E → F => iteratedFDeriv ℝ n f 0 u) he
  rw [A.iteratedFDeriv_comp_diagonal, B.iteratedFDeriv_comp_diagonal] at hj
  simp only [hA, hB, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin] at hj
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply smul_right_injective (M := F) hn
  simpa only [Nat.cast_smul_eq_nsmul] using hj

end RothschildStein.G3
