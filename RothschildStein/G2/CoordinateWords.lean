-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DifferentialTranspose
public import RothschildStein.S.ClassicalWords
public import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ}

/-- Smooth scalar functions, used only to express permutation of coordinate derivatives. -/
abbrev SmoothScalar (N : ℕ) := {f : (Fin N → ℝ) → ℝ // ContDiff ℝ (⊤ : ℕ∞) f}

/-- A coordinate derivative acting on smooth scalar functions. -/
def coordinateAction (j : Fin N) (f : SmoothScalar N) : SmoothScalar N :=
  ⟨fun x => fderiv ℝ f.1 x (Hormander.Interface.basisVec j),
    (f.2.fderiv_right (by simp)).clm_apply contDiff_const⟩

/-- Smooth coordinate derivatives commute (BB p. 106). -/
theorem coordinateAction_comm (i j : Fin N) (f : SmoothScalar N) :
    coordinateAction i (coordinateAction j f) = coordinateAction j (coordinateAction i f) := by
  apply Subtype.ext
  funext x
  have h := VectorField.fderiv_apply_lieBracket f.2.contDiffAt (by simp)
    (differentiableAt_const (c := Hormander.Interface.basisVec j))
    (differentiableAt_const (c := Hormander.Interface.basisVec i)) (x := x)
  rw [VectorField.lieBracket_eq] at h
  dsimp only at h
  rw [(hasFDerivAt_const (𝕜 := ℝ) (Hormander.Interface.basisVec j) x).fderiv,
    (hasFDerivAt_const (𝕜 := ℝ) (Hormander.Interface.basisVec i) x).fderiv] at h
  simp only [zero_apply, sub_self, map_zero] at h
  change fderiv ℝ (fun z => fderiv ℝ f.1 z (Hormander.Interface.basisVec j)) x
    (Hormander.Interface.basisVec i) =
    fderiv ℝ (fun z => fderiv ℝ f.1 z (Hormander.Interface.basisVec i)) x
      (Hormander.Interface.basisVec j)
  exact sub_eq_zero.mp h.symm

/-- A coordinate word is unaffected by permutation (BB p. 106). -/
theorem coordinateWord_perm (l l' : List (Fin N)) (h : l.Perm l') (f : SmoothScalar N) :
    l.foldr coordinateAction f = l'.foldr coordinateAction f := by
  let : LeftCommutative (coordinateAction (N := N)) := ⟨coordinateAction_comm⟩
  exact h.foldr_eq f

/-- The finite coordinate word appearing in the multi-index derivative. -/
def coordinateWord (a : Fin N → ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun j => List.replicate (a j) j

/-- Coordinate-word actions coincide with raw iterated coordinate derivatives. -/
theorem coordinateWord_coe (l : List (Fin N)) (f : SmoothScalar N) :
    (l.foldr coordinateAction f).1 = l.foldr
      (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f.1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, coordinateAction, ih]

/-- Reversing the coordinate word does not change a multi-index derivative
(BB transpose formula, pp. 106–108). -/
theorem coordinateWord_reverse (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ((coordinateWord a).reverse.foldr
      (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f) = euclideanPartial a f := by
  have h := congrArg (fun g : SmoothScalar N => g.1)
    (coordinateWord_perm (coordinateWord a).reverse (coordinateWord a)
      (List.reverse_perm _) ⟨f, hf⟩)
  simpa only [coordinateWord_coe, coordinateWord, euclideanPartial] using h

end RothschildStein.G2
