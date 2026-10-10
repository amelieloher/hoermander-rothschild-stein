-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Data.Set.Card

/-! Overlap bounds when a selected family is indexed by its subtype. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace HeatKernel

/-- Restricting the index type to the selected centers preserves finiteness and the
overlap cardinal bound. -/
theorem finite_ncard_subtype_overlap {E ι : Type*} (C : Set ι) (A : ι → Set E)
    (x : E) (M : ℕ) (hf : {i ∈ C | x ∈ A i}.Finite)
    (hcard : {i ∈ C | x ∈ A i}.ncard ≤ M) :
    {i : C | x ∈ A i.val}.Finite ∧ {i : C | x ∈ A i.val}.ncard ≤ M := by
  have hpre := hf.preimage (f := fun i : C => i.val)
    (fun _ _ _ _ h => Subtype.ext h)
  have hfinite : {i : C | x ∈ A i.val}.Finite := by
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using hpre
  refine ⟨hfinite, ?_⟩
  exact (Set.ncard_le_ncard_of_injOn (t := {i ∈ C | x ∈ A i}) (fun i : C => i.val)
    (fun i hi => ⟨i.property, hi⟩)
    (fun _ _ _ _ h => Subtype.ext h) hf).trans hcard

end HeatKernel
