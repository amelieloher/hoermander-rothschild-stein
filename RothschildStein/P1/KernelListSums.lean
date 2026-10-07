-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeClosure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N} {m lam : ℕ}

/-- Finite list sums of regular kernels preserve multiplicities
and the actual regularity budget. -/
theorem IsRegularKernel.listSum {ι : Type*} (l : List ι)
    (r : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hr : ∀ i ∈ l, IsRegularKernel F m (r i)) :
    IsRegularKernel F m (fun ξ η => (l.map (fun i => r i ξ η)).sum) := by
  induction l with
  | nil => simpa using (IsRegularKernel.zero : IsRegularKernel F m (fun _ _ => 0))
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hr i List.mem_cons_self).add
      (ih (fun j hj => hr j (List.mem_cons_of_mem i hj)))

/-- Finite list sums of type kernels preserve multiplicities,
including type zero; this is a kernel statement. -/
theorem IsTypeKernel.listSum {ι : Type*} (l : List ι)
    (r : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hr : ∀ i ∈ l, IsTypeKernel F lam (r i)) :
    IsTypeKernel F lam (fun ξ η => (l.map (fun i => r i ξ η)).sum) := by
  induction l with
  | nil => simpa using (IsTypeKernel.zero : IsTypeKernel F lam (fun _ _ => 0))
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hr i List.mem_cons_self).add
      (ih (fun j hj => hr j (List.mem_cons_of_mem i hj)))

/-- A kernel regular at every budget is of every nonnegative type. -/
theorem isTypeKernel_of_all_regular (lam : ℕ)
    (r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hr : ∀ budget, IsRegularKernel F budget r) : IsTypeKernel F lam r := by
  intro budget
  refine ⟨{
    principal := []
    principal_degree := by simp
    regular := r
    regular_isRegular := hr budget
    eq_off_diagonal := ?_ }⟩
  intro ξ η _
  simp

/-- A type decomposition transfers along equality off the diagonal. -/
theorem IsTypeKernel.congr_off_diagonal
    {r q : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsTypeKernel F lam r)
    (he : ∀ ξ η, ξ ≠ η → r ξ η = q ξ η) : IsTypeKernel F lam q := by
  intro budget
  obtain ⟨d⟩ := hr budget
  refine ⟨{ d with eq_off_diagonal := ?_ }⟩
  intro ξ η hne
  rw [← he ξ η hne]
  exact d.eq_off_diagonal ξ η hne

end RothschildStein.P1
