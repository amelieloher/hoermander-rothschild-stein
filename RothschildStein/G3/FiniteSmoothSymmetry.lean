-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteSmoothAdjacentSymmetry

@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem tuple_function_perm_invariant_of_adjacent
    {E F : Type*} {n : ℕ} (A : (Fin (n + 1) → E) → F)
    (hA : ∀ u (i : Fin n), A (fun j => u (Equiv.swap i.castSucc i.succ j)) = A u)
    (σ : Equiv.Perm (Fin (n + 1))) (u : Fin (n + 1) → E) :
    A (fun j => u (σ j)) = A u := by
  let S : Submonoid (Equiv.Perm (Fin (n + 1))) :=
    { carrier := {σ | ∀ u, A (fun j => u (σ j)) = A u}
      one_mem' := by intro u; rfl
      mul_mem' := by
        intro σ τ hσ hτ u
        change A (fun j => u (σ (τ j))) = A u
        rw [hτ (fun j => u (σ j)), hσ u] }
  have hle : Submonoid.closure
      (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) ≤ S := by
    apply Submonoid.closure_le.mpr
    rintro σ ⟨i, rfl⟩
    exact fun u => hA u i
  have hmem : σ ∈ S := hle (by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial)
  exact hmem u

theorem iteratedFDeriv_perm_of_finite_smoothness
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {n : ℕ} {x : E} (hf : ContDiffAt ℝ n f x)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → E) :
    iteratedFDeriv ℝ n f x (fun j => u (σ j)) = iteratedFDeriv ℝ n f x u := by
  cases n with
  | zero =>
    congr 1
    ext i
    exact Fin.elim0 i
  | succ n =>
    exact tuple_function_perm_invariant_of_adjacent _
      (fun u i => iteratedFDeriv_adjacent_swap n hf u i) σ u

end RothschildStein.G3
