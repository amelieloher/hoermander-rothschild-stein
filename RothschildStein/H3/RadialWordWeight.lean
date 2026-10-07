-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialWordTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- Nonempty gauge factors have total weight at least their count. -/
theorem radial_factors_length_le_weight {m : ℕ} (w : Fin m → ℕ+)
    (Ks : List (List (Fin m))) (hKs : ∀ K ∈ Ks, K ≠ []) :
    Ks.length ≤ (Ks.map (wordWeight w)).sum := by
  induction Ks with
  | nil => simp
  | cons K Ks ih =>
    have hK : 1 ≤ wordWeight w K :=
      (List.length_pos_iff.mpr (hKs K (List.mem_cons_self ..))).trans_le
        (RothschildStein.S.length_le_wordWeight w K)
    have ht := ih (fun L hL => hKs L (List.mem_cons_of_mem _ hL))
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

/-- Every term for a nonempty input word differentiates the profile at
least once, so no order-zero profile bound is needed. -/
theorem radialWordTerms_profile_pos {m : ℕ} (w : Fin m → ℕ+)
    (I : List (Fin m)) (hI : I ≠ []) {t : ℕ × List (List (Fin m))}
    (ht : t ∈ radialWordTerms I) : 0 < t.1 := by
  obtain ⟨hlen,hweight,_⟩ := radialWordTerms_metadata w I ht
  have hpos : 0 < wordWeight w I :=
    (List.length_pos_iff.mpr hI).trans_le (RothschildStein.S.length_le_wordWeight w I)
  by_contra h
  have hj : t.1 = 0 := Nat.eq_zero_of_not_pos h
  have hKs : t.2 = [] := List.eq_nil_of_length_eq_zero (hlen.symm.trans hj)
  simp only [hKs,List.map_nil,List.sum_nil] at hweight
  omega

end RothschildStein.H3
