-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HomogeneousOperators
public import RothschildStein.S.ClassicalWords
public import RothschildStein.Definitions.wordWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3
open G2
variable {N m : ℕ} {G : HomogeneousGroup N}

/-- Every classical word in homogeneous smooth fields is a
homogeneous operator of its fixed weighted word degree (BB p. 107). -/
theorem wordDerivative_homogeneous (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hh : ∀ i, IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ)) (I : List (Fin m)) :
    IsHomogeneousOperator G (wordDerivative Y I) (wordWeight w I) := by
  induction I with
  | nil =>
    intro f hf t ht x
    simp only [wordDerivative, wordWeight, List.map_nil, List.sum_nil,
      Nat.cast_zero, Real.rpow_zero, one_mul, Function.comp_apply]
  | cons i I ih =>
    have htail : PreservesSmooth (wordDerivative Y I) := by
      intro f hf
      exact contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Y
        (fun j => (hs j).contDiffOn) I f hf.contDiffOn)
    have hscalar : ∀ c f, fieldDerivative (Y i) (fun x => c * f x) =
        fun x => c * fieldDerivative (Y i) f x := by
      intro c f
      funext x
      unfold fieldDerivative
      change fderiv ℝ (c • f) x (Y i x) = _
      rw [fderiv_const_smul_field]
      rfl
    have hcomp := ((isHomogeneousField_iff_operator G (Y i) _).mp (hh i)).comp G ih htail hscalar
    change IsHomogeneousOperator G (wordDerivative Y (i :: I))
      (((w i : ℕ) : ℝ) + (wordWeight w I : ℝ)) at hcomp
    simpa only [wordWeight, List.map_cons, List.sum_cons, Nat.cast_add] using hcomp

/-- The weighted word's cutoff factor is the inverse radius to
exactly its word weight (BB Lemma 8.40 proof, p. 370). -/
theorem wordDerivative_cutoff_dilation (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hh : ∀ i, IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ))
    (I : List (Fin m)) {χ : (Fin N → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    wordDerivative Y I (χ ∘ G.dilate ε⁻¹) x =
      ε ^ (-(wordWeight w I : ℝ)) * wordDerivative Y I χ (G.dilate ε⁻¹ x) := by
  rw [wordDerivative_homogeneous w Y hs hh I χ hχ ε⁻¹ (inv_pos.mpr hε) x,
    Real.inv_rpow hε.le, Real.rpow_neg hε.le]

end RothschildStein.H3
