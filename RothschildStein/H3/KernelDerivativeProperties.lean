-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelDerivativeSeminorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ}

/-- Increasing the Euclidean derivative budget increases the exact
finite maximum Λ_{T,k} (BB Definition 8.13, p. 346). -/
theorem kernelDerivativeBound_mono (ν T : (Fin N → ℝ) → ℝ)
    {k l : ℕ} (hkl : k ≤ l) : kernelDerivativeBound ν T k ≤ kernelDerivativeBound ν T l := by
  unfold kernelDerivativeBound
  apply (Finset.sup'_le_iff _ _).mpr
  intro a _
  exact kernelSphereBound_partial_le (fun j => (a.val j).val) (a.property.trans hkl)

/-- At derivative budget zero the finite maximum is exactly the
zeroth-order sphere maximum, rather than a separate bound (BB (8.7)). -/
theorem kernelDerivativeBound_zero (ν T : (Fin N → ℝ) → ℝ) :
    kernelDerivativeBound ν T 0 = kernelSphereBound ν T := by
  have hp (a : KernelPartialIndex N 0) : (fun j => (a.val j).val) = fun _ => 0 := by
    funext j
    exact Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun i _ => Nat.zero_le ((a.val i).val))
        (Finset.mem_univ j)).trans a.property)
  have hpartial (a : KernelPartialIndex N 0) :
      euclideanPartial (fun j => (a.val j).val) T = T := by
    rw [hp a]
    have he : (List.finRange N).flatMap (fun _ => ([] : List (Fin N))) = [] := by
      induction List.finRange N with
      | nil => rfl
      | cons j l ih => simpa only [List.flatMap_cons, List.nil_append] using ih
    simp only [euclideanPartial, List.replicate_zero, he, List.foldr_nil]
  unfold kernelDerivativeBound
  have he : (fun a : KernelPartialIndex N 0 =>
      kernelSphereBound ν (euclideanPartial (fun j => (a.val j).val) T)) =
      fun _ => kernelSphereBound ν T := by
    funext a
    rw [hpartial a]
  rw [he, Finset.sup'_const]

end RothschildStein.H3
