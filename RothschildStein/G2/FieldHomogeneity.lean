-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.OperatorInvariance
public import RothschildStein.G2.FieldCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The linear differential of the coordinate dilation. -/
def dilationDifferential (t : ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun j => t ^ G.weight j • ContinuousLinearMap.proj j

/-- The linear differential acts exactly as the coordinate dilation. -/
theorem dilationDifferential_apply (t : ℝ) (v : Fin N → ℝ) :
    dilationDifferential G t v = G.dilate t v := rfl

/-- Coordinate dilations are differentiable with their linear differential. -/
theorem hasFDerivAt_dilate (t : ℝ) (x : Fin N → ℝ) :
    HasFDerivAt (G.dilate t) (dilationDifferential G t) x := by
  apply hasFDerivAt_pi.mpr
  intro j
  exact (hasFDerivAt_apply j x).const_smul (t ^ G.weight j)

/-- Coordinate dilations are smooth. -/
theorem contDiff_dilate (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (G.dilate t) :=
  contDiff_pi.mpr fun j => (contDiff_apply ℝ ℝ j).const_smul (t ^ G.weight j)

/-- Homogeneity of a vector field in tangent-vector form
(BB Proposition 3.23, p. 107). -/
def IsHomogeneousField (V : (Fin N → ℝ) → (Fin N → ℝ)) (degree : ℝ) : Prop :=
  ∀ t, 0 < t → ∀ x, G.dilate t (V x) = t ^ degree • V (G.dilate t x)

/-- Tangent homogeneity is precisely homogeneity of the differentiation operator
(BB Proposition 3.23, p. 107). -/
theorem isHomogeneousField_iff_operator
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (degree : ℝ) :
    IsHomogeneousField G V degree ↔ IsHomogeneousOperator G (fieldDerivative V) degree := by
  constructor
  · intro h f hf t ht x
    unfold fieldDerivative
    rw [fderiv_comp x (hf.differentiable (by simp)).differentiableAt
      (hasFDerivAt_dilate G t x).differentiableAt]
    rw [(hasFDerivAt_dilate G t x).fderiv]
    change fderiv ℝ f (G.dilate t x) (dilationDifferential G t (V x)) = _
    rw [dilationDifferential_apply, h t ht x, map_smul]
    rfl
  · intro h t ht x
    ext j
    have hj := h (fun x => x j) (contDiff_apply ℝ ℝ j) t ht x
    unfold fieldDerivative at hj
    rw [fderiv_comp x (differentiableAt_apply j (G.dilate t x))
      (hasFDerivAt_dilate G t x).differentiableAt] at hj
    rw [(hasFDerivAt_dilate G t x).fderiv] at hj
    rw [(hasFDerivAt_apply j (G.dilate t x)).fderiv] at hj
    simpa only [ ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, dilationDifferential_apply, Pi.smul_apply,
      smul_eq_mul] using hj

/-- Dilation covariance of prescribed left-invariant fields
(BB Theorem 3.29, p. 111). -/
theorem dilate_leftField (t : ℝ) (ht : 0 < t) (v x : Fin N → ℝ) :
    G.dilate t (leftField G v x) = leftField G (G.dilate t v) (G.dilate t x) := by
  have he : G.dilate t ∘ G.mul x = G.mul (G.dilate t x) ∘ G.dilate t := by
    funext y
    exact dilate_product G ht x y
  have hd₁ := fderiv_comp 0 (hasFDerivAt_dilate G t (G.mul x 0)).differentiableAt
    ((contDiff_leftTranslation G x).differentiable (by simp)).differentiableAt
  have hd₂ := fderiv_comp 0
    ((contDiff_leftTranslation G (G.dilate t x)).differentiable (by simp)).differentiableAt
    (hasFDerivAt_dilate G t 0).differentiableAt
  rw [he, hd₂, (hasFDerivAt_dilate G t (G.mul x 0)).fderiv,
    (hasFDerivAt_dilate G t 0).fderiv, dilate_zero G t] at hd₁
  exact (congrArg (fun L => L v) hd₁).symm

/-- The canonical left-invariant field has its coordinate weight as degree
(BB Theorem 3.29, p. 110). -/
theorem canonicalField_homogeneous (j : Fin N) :
    IsHomogeneousField G (G.canonicalField j) (G.weight j) := by
  intro t ht x
  rw [canonicalField_eq_leftField, dilate_leftField G t ht]
  have hb : G.dilate t (Hormander.Interface.basisVec j) =
      t ^ G.weight j • Hormander.Interface.basisVec j := by
    ext k
    simp [HomogeneousGroup.dilate, coordinateDilation, Hormander.Interface.basisVec,
      Pi.single_apply]
    split_ifs <;> simp_all
  rw [hb]
  simp [leftField, map_smul, Real.rpow_natCast]

end RothschildStein.G2
