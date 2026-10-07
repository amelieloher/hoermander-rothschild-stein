-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialWordExpansion
public import RothschildStein.H3.RadialGapPower

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set

/-- The finite coefficient sum for one fixed word; it contains no
 center or radius parameters. -/
def radialWordBoundConstant {m : ℕ} (κ : ℕ → ℝ)
    (M : List (Fin m) → ℝ) (I : List (Fin m)) : ℝ :=
  ((radialWordTerms I).map (fun t => κ t.1*2^t.1*(t.2.map M).prod)).sum

private theorem abs_list_sum_weighted {α : Type*} (l : List α)
    (f C : α → ℝ) (b : ℝ) (h : ∀ a ∈ l, |f a| ≤ C a*b) :
    |(l.map f).sum| ≤ (l.map C).sum*b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons]
    calc
      |f a+(l.map f).sum| ≤ |f a|+|(l.map f).sum| := abs_add_le _ _
      _ ≤ C a*b+(l.map C).sum*b := add_le_add (h a (List.mem_cons_self ..)) ht
      _ = _ := by ring

/-- The fixed-word coefficient is nonnegative. -/
theorem radialWordBoundConstant_nonneg {m : ℕ} (κ : ℕ → ℝ)
    (M : List (Fin m) → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hM : ∀ K, 0 ≤ M K)
    (I : List (Fin m)) : 0 ≤ radialWordBoundConstant κ M I := by
  apply List.sum_nonneg
  intro c hc
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hc
  have hp : 0 ≤ (t.2.map M).prod := List.prod_nonneg (by
    intro b hb
    obtain ⟨K,_,rfl⟩ := List.mem_map.mp hb
    exact hM K)
  exact mul_nonneg (mul_nonneg (hκ t.1) (pow_nonneg (by norm_num) _)) hp

/-- The finite expansion yields the exact fixed-word gap bound.
 Its constant depends only on the profile and gauge word constants. -/
theorem wordDerivative_radial_gap_bound {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ν : (Fin n → ℝ) → ℝ}
    (hν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (w : Fin m → ℕ+)
    (κ : ℕ → ℝ) (M : List (Fin m) → ℝ)
    (hκ : ∀ j, 0 ≤ κ j) (hM : ∀ K, 0 ≤ M K) (I : List (Fin m))
    {x : Fin n → ℝ} (hx : x ≠ 0) {a : ℝ} (ha : 0 < a) (hav : a ≤ ν x)
    (hg : ∀ K, |wordDerivative X K ν x| ≤ M K*(ν x)^(1-(wordWeight w K : ℝ)))
    (hp : ∀ t ∈ radialWordTerms I, |iteratedDeriv t.1 F (ν x)| ≤ κ t.1*(2/a)^t.1) :
    |wordDerivative X I (F ∘ ν) x| ≤ radialWordBoundConstant κ M I*a^(-(wordWeight w I : ℝ)) := by
  rw [wordDerivative_radial_expansion X hX hν hF I hx]
  apply abs_list_sum_weighted
  intro t ht
  obtain ⟨hcount,hweight,hne⟩ := radialWordTerms_metadata w I ht
  have hb := radialTerm_abs_bound X ν F w M t x ha hav (hκ t.1) hcount hne
    (fun K _ => hM K) (fun K _ => hg K) (hp t ht)
  simpa only [hweight] using hb

end RothschildStein.H3
