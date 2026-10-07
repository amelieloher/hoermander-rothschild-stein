-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.CutoffChains

@[expose] public section

namespace Hormander.E

/-- A data-bearing finite path of nested cutoffs, with every intermediate
support retained inside the fixed frame set. -/
inductive CutoffPathInside {N : ℕ} (K : Set (EuclideanSpace ℝ (Fin N))) :
    ℕ → (EuclideanSpace ℝ (Fin N) → ℝ) → (EuclideanSpace ℝ (Fin N) → ℝ) → Type where
  | base {η η'} (hηη' : Hormander.D.cutoffPrecedes η η')
      (hη'K : tsupport η' ⊆ K) : CutoffPathInside K 0 η η'
  | insert {n η ξ η'} (hηξ : Hormander.D.cutoffPrecedes η ξ)
      (hξK : tsupport ξ ⊆ K) (hrest : CutoffPathInside K n ξ η') :
      CutoffPathInside K (n + 1) η η'

/-- Construct an explicit finite path of any prescribed number of nested
cutoffs while keeping each intermediate support inside the outer frame set. -/
noncomputable def exists_cutoff_path_inside
    {N : ℕ} {K : Set (EuclideanSpace ℝ (Fin N))}
    {η η' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hηη' : Hormander.D.cutoffPrecedes η η') (hη'K : tsupport η' ⊆ K) :
    ∀ n : ℕ, CutoffPathInside K n η η' := by
  intro n
  induction n generalizing η with
  | zero => exact .base hηη' hη'K
  | succ n ih =>
      let hchoice := Hormander.D.exists_intermediate_cutoff hηη'
      let ξ := Classical.choose hchoice
      have hξ := Classical.choose_spec hchoice
      rcases hξ with ⟨hηξ, hξη', _⟩
      have hξK : tsupport ξ ⊆ K :=
        (cutoffPrecedes_tsupport_subset hξη').trans hη'K
      exact .insert hηξ hξK (ih hξη')

/-- The endpoints of a finite cutoff path satisfy the original nesting
relation. -/
theorem CutoffPathInside.precedes_outer
    {N : ℕ} {K : Set (EuclideanSpace ℝ (Fin N))}
    {n : ℕ} {η η' : EuclideanSpace ℝ (Fin N) → ℝ}
    (p : CutoffPathInside K n η η') : Hormander.D.cutoffPrecedes η η' := by
  induction p with
  | base hηη' _ => exact hηη'
  | insert hηξ _ _ ih => exact Hormander.D.cutoffPrecedes.trans hηξ ih

end Hormander.E

end
