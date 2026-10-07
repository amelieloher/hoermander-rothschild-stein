-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- Product-rule factor lists: differentiate each factor once, retaining
 factor order and repetitions. -/
def radialFactorDerivatives {m : ℕ} (i : Fin m) :
    List (List (Fin m)) → List (List (List (Fin m)))
  | [] => []
  | K :: Ks => ((i :: K) :: Ks) :: (radialFactorDerivatives i Ks).map (K :: ·)

/-- The finite chain-rule expansion indices for a scalar profile composed
 with a gauge. Repeated terms encode their integer multiplicities. -/
def radialWordTerms {m : ℕ} : List (Fin m) → List (ℕ × List (List (Fin m)))
  | [] => [(0,[])]
  | i :: I => (radialWordTerms I).flatMap fun t =>
      (t.1+1,[i] :: t.2) :: (radialFactorDerivatives i t.2).map (fun Ks => (t.1,Ks))

/-- Differentiating one factor preserves the number of factors. -/
theorem radialFactorDerivatives_length {m : ℕ} (i : Fin m)
    (Ks : List (List (Fin m))) {Ls : List (List (Fin m))}
    (h : Ls ∈ radialFactorDerivatives i Ks) : Ls.length = Ks.length := by
  induction Ks generalizing Ls with
  | nil => simp [radialFactorDerivatives] at h
  | cons K Ks ih =>
    simp only [radialFactorDerivatives,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨Z,hZ,rfl⟩
    · rfl
    · simp only [List.length_cons,ih hZ]

/-- Differentiating one factor adds exactly the weight of the new letter. -/
theorem radialFactorDerivatives_weight {m : ℕ} (w : Fin m → ℕ+)
    (i : Fin m) (Ks : List (List (Fin m))) {Ls : List (List (Fin m))}
    (h : Ls ∈ radialFactorDerivatives i Ks) :
    (Ls.map (wordWeight w)).sum = (w i : ℕ) + (Ks.map (wordWeight w)).sum := by
  induction Ks generalizing Ls with
  | nil => simp [radialFactorDerivatives] at h
  | cons K Ks ih =>
    simp only [radialFactorDerivatives,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨Z,hZ,rfl⟩
    · simp [wordWeight,Nat.add_assoc]
    · simp only [List.map_cons,List.sum_cons,ih hZ]
      omega

/-- The product-rule factors remain nonempty words. -/
theorem radialFactorDerivatives_nonempty {m : ℕ} (i : Fin m)
    (Ks : List (List (Fin m))) (hKs : ∀ K ∈ Ks, K ≠ [])
    {Ls : List (List (Fin m))} (h : Ls ∈ radialFactorDerivatives i Ks) :
    ∀ L ∈ Ls, L ≠ [] := by
  induction Ks generalizing Ls with
  | nil => simp [radialFactorDerivatives] at h
  | cons K Ks ih =>
    simp only [radialFactorDerivatives,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨Z,hZ,rfl⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · simp
      · exact hKs L (List.mem_cons_of_mem _ hL)
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hKs _ (List.mem_cons_self ..)
      · exact ih (fun L hL => hKs L (List.mem_cons_of_mem _ hL)) hZ L hL

/-- Every expansion term has one gauge factor per profile
 derivative, total weight equal to the input word, and no empty factor. -/
theorem radialWordTerms_metadata {m : ℕ} (w : Fin m → ℕ+)
    (I : List (Fin m)) {t : ℕ × List (List (Fin m))} (ht : t ∈ radialWordTerms I) :
    t.1 = t.2.length ∧ (t.2.map (wordWeight w)).sum = wordWeight w I ∧
      ∀ K ∈ t.2, K ≠ [] := by
  induction I generalizing t with
  | nil =>
    simp only [radialWordTerms,List.mem_singleton] at ht
    subst t
    simp [wordWeight]
  | cons i I ih =>
    simp only [radialWordTerms,List.mem_flatMap] at ht
    obtain ⟨s,hs,ht⟩ := ht
    obtain ⟨hlen,hweight,hne⟩ := ih hs
    simp only [List.mem_cons,List.mem_map] at ht
    rcases ht with rfl | ⟨Ks,hKs,rfl⟩
    · refine ⟨by simp [hlen],?_,?_⟩
      · simp [wordWeight,hweight]
      · intro K hK
        rcases List.mem_cons.mp hK with rfl | hK
        · simp
        · exact hne K hK
    · refine ⟨hlen.trans (radialFactorDerivatives_length i s.2 hKs).symm,?_,?_⟩
      · rw [radialFactorDerivatives_weight w i s.2 hKs,hweight]
        simp [wordWeight]
      · exact radialFactorDerivatives_nonempty i s.2 hne hKs

end RothschildStein.H3
