-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedHomogeneity
public import RothschildStein.H1.FirstNondegeneracy
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The weighted length of a differential word counts drift
letters twice and horizontal letters once (BB Theorem 6.20(1), p. 270). -/
def differentialWordWeight (I : List (Fin (q + 1))) : ℕ :=
  (I.map fun i => if i = 0 then 2 else 1).sum

/-- All differential words of the standing fields preserve
punctured smoothness (BB Theorem 6.20(1), p. 270). -/
theorem StandingHypotheses.wordDerivative_smooth_off_zero
    (H : StandingHypotheses G q) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : Fin N → ℝ)}ᶜ))
    (I : List (Fin (q + 1))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordDerivative H.fields I f) ({(0 : Fin N → ℝ)}ᶜ) :=
  S.contDiffOn_wordDerivative ⟨_, isOpen_compl_singleton⟩ H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) I f hf

/-- Every differential word lowers the kernel's degree by its
weighted length, including every occurrence of the drift (BB p. 270). -/
theorem StandingHypotheses.wordDerivative_homogeneous
    (H : StandingHypotheses G q) {a : ℝ} {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    (I : List (Fin (q + 1))) :
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      wordDerivative H.fields I f (G.dilate t x) =
        t ^ (a - (differentialWordWeight I : ℝ)) * wordDerivative H.fields I f x := by
  induction I with
  | nil => simpa only [differentialWordWeight, List.map_nil, List.sum_nil,
      Nat.cast_zero, sub_zero, wordDerivative] using hh
  | cons i I ih =>
    intro t ht x hx
    have he := fieldDerivative_punctured_homogeneous G (H.homogeneous i)
      (H.wordDerivative_smooth_off_zero G hf I) ih ht hx
    have hw : (differentialWordWeight (i :: I) : ℝ) =
        (if i = 0 then 2 else 1) + (differentialWordWeight I : ℝ) := by
      simp only [differentialWordWeight, List.map_cons, List.sum_cons, Nat.cast_add]
      split_ifs <;> norm_num
    rw [hw]
    convert he using 1 <;> simp only [wordDerivative]
    congr 2
    ring

end RothschildStein.H1
