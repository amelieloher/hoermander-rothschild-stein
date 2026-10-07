-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TaylorCompositionCongruence
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def chronologicalComposition : List (E → E) → E → E
  | [] => id
  | f :: fs => chronologicalComposition fs ∘ f

theorem chronologicalComposition_contDiffAt {n : ℕ} (fs : List (E → E))
    (hs : ∀ f ∈ fs, ContDiffAt ℝ n f 0) (hz : ∀ f ∈ fs, f 0 = 0) :
    ContDiffAt ℝ n (chronologicalComposition fs) 0 := by
  induction fs with
  | nil => exact contDiffAt_id
  | cons f fs ih =>
    apply ContDiffAt.comp (f := f)
    · rw [hz f List.mem_cons_self]
      exact ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
        (fun g hg => hz g (List.mem_cons_of_mem f hg))
    · exact hs f List.mem_cons_self

/-- Pairwise jet identities on one family collapse any finite chronological
list to its algebraic product; the list length does not change the jet order. -/
theorem chronologicalComposition_jets_eq_product {A : Type*} [Zero A] {n : ℕ}
    (op : A → A → A) (F : A → E → E)
    (hs : ∀ a, ContDiffAt ℝ n (F a) 0) (hz : ∀ a, F a 0 = 0)
    (hbase : ∀ k ≤ n, iteratedFDeriv ℝ k (F 0) 0 = iteratedFDeriv ℝ k id 0)
    (hpair : ∀ a b, ∀ k ≤ n, iteratedFDeriv ℝ k (F b ∘ F a) 0 =
      iteratedFDeriv ℝ k (F (op a b)) 0)
    (as : List A) : ∀ k ≤ n,
    iteratedFDeriv ℝ k (chronologicalComposition (as.map F)) 0 =
      iteratedFDeriv ℝ k (F (as.foldr op 0)) 0 := by
  induction as with
  | nil => intro k hk; exact (hbase k hk).symm
  | cons a as ih =>
    have htail : ContDiffAt ℝ n (chronologicalComposition (as.map F)) 0 := by
      apply chronologicalComposition_contDiffAt
      · intro f hf; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hf; exact hs b
      · intro f hf; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hf; exact hz b
    have he := frechet_jets_substitution_eq (hs a) (hz a) htail (hs (as.foldr op 0)) ih
    intro k hk
    exact (he k hk).trans (hpair a (as.foldr op 0) k hk)
end RothschildStein.G3
