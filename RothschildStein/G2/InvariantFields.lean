-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Foundation
public import RothschildStein.Definitions.HomogeneousGroup.canonicalField
public import RothschildStein.Definitions.fieldDerivative
public import Mathlib.Analysis.Calculus.VectorField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The left-invariant field with prescribed value at the identity
(BB (3.9), p. 108). -/
def leftField (v : Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ (G.mul x) 0 v

/-- The right-invariant field with prescribed value at the identity
(BB (3.10), p. 109). -/
def rightField (v : Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fderiv ℝ (fun y => G.mul y x) 0 v

/-- Invariance expressed by covariance of tangent vectors
(BB (3.15), p. 112). -/
def IsLeftInvariantField (V : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ x y, fderiv ℝ (G.mul x) y (V y) = V (G.mul x y)

/-- Right translation covariance (BB Proposition 3.26, p. 109). -/
def IsRightInvariantField (V : (Fin N → ℝ) → (Fin N → ℝ)) : Prop :=
  ∀ x y, fderiv ℝ (fun z => G.mul z x) y (V y) = V (G.mul y x)

/-- Left translations are smooth. -/
theorem contDiff_leftTranslation (x : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (G.mul x) :=
  contDiff_pi.mpr fun k => (contDiff_eval (G.productPolynomial k)).comp
    (contDiff_pi.mpr fun i => Sum.casesOn i
      (fun _ => contDiff_const) (fun j => contDiff_apply ℝ ℝ j))

/-- Right translations are smooth. -/
theorem contDiff_rightTranslation (x : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => G.mul y x) :=
  contDiff_pi.mpr fun k => (contDiff_eval (G.productPolynomial k)).comp
    (contDiff_pi.mpr fun i => Sum.casesOn i
      (fun j => contDiff_apply ℝ ℝ j) (fun _ => contDiff_const))

/-- The canonical field is the field prescribed by a coordinate vector
(BB Theorem 3.29, p. 110). -/
theorem canonicalField_eq_leftField (j : Fin N) :
    G.canonicalField j = leftField G (Hormander.Interface.basisVec j) := rfl

/-- Prescribed left-invariant fields are smooth (BB Proposition 3.26, p. 109). -/
theorem contDiff_leftField (v : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (leftField G v) := by
  exact ((contDiff_mul G).fderiv (g := fun _ => 0) contDiff_const (by simp)).clm_apply
    contDiff_const

/-- Prescribed right-invariant fields are smooth (BB Proposition 3.26, p. 109). -/
theorem contDiff_rightField (v : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rightField G v) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.2 p.1) :=
    contDiff_pi.mpr fun k => (contDiff_eval (G.productPolynomial k)).comp
      (contDiff_pi.mpr fun i => Sum.casesOn i
        (fun j => (contDiff_apply ℝ ℝ j).comp contDiff_snd)
        (fun j => (contDiff_apply ℝ ℝ j).comp contDiff_fst))
  exact (h.fderiv (g := fun _ => 0) contDiff_const (by simp)).clm_apply contDiff_const

/-- Evaluation at the identity recovers the prescribed tangent vector
(BB Proposition 3.26, p. 109). -/
theorem leftField_zero (v : Fin N → ℝ) : leftField G v 0 = v := by
  have h : G.mul 0 = id := funext (zero_mul G)
  simp [leftField, h]

/-- Associativity differentiated at the identity proves left invariance
(BB Proposition 3.26, p. 109). -/
theorem leftField_invariant (v : Fin N → ℝ) : IsLeftInvariantField G (leftField G v) := by
  intro x y
  have he : G.mul x ∘ G.mul y = G.mul (G.mul x y) := by
    funext z
    exact (mul_assoc G x y z).symm
  have hx := (contDiff_leftTranslation G x).differentiable (by simp)
  have hy := (contDiff_leftTranslation G y).differentiable (by simp)
  have hd := fderiv_comp 0 (hx.differentiableAt) (hy.differentiableAt)
  rw [he, mul_zero G y] at hd
  exact (congrArg (fun L => L v) hd).symm

/-- Associativity also proves right invariance (BB p. 109). -/
theorem rightField_invariant (v : Fin N → ℝ) : IsRightInvariantField G (rightField G v) := by
  intro x y
  have he : (fun z => G.mul z x) ∘ (fun z => G.mul z y) =
      (fun z => G.mul z (G.mul y x)) := by
    funext z
    exact mul_assoc G z y x
  have hx := (contDiff_rightTranslation G x).differentiable (by simp)
  have hy := (contDiff_rightTranslation G y).differentiable (by simp)
  have hd := fderiv_comp 0 (hx.differentiableAt) (hy.differentiableAt)
  rw [he, zero_mul G y] at hd
  exact (congrArg (fun L => L v) hd).symm

/-- A left-invariant field is determined by its value at the identity
(BB Proposition 3.26, p. 109). -/
theorem IsLeftInvariantField.eq_leftField {V : (Fin N → ℝ) → (Fin N → ℝ)}
    (h : IsLeftInvariantField G V) : V = leftField G (V 0) := by
  funext x
  simpa only [leftField, mul_zero G x] using (h x 0).symm

end RothschildStein.G2
