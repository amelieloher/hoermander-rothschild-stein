-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.fieldDerivative
public import RothschildStein.Definitions.fieldTranspose
public import RothschildStein.Definitions.wordTransposeTest
public import RothschildStein.Definitions.wordTranspose
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Coordinate expansion of a linear differential (BB (2.2), p. 68). -/
theorem differential_coordinates (A : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    A v = ∑ j : Fin n, v j * A (Hormander.Interface.basisVec j) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : Pi.single j (v j) = v j • Hormander.Interface.basisVec j := by
    ext k
    by_cases hk : k = j <;> simp [Hormander.Interface.basisVec, hk]
  rw [h, map_smul]
  rfl

/-- The scalar transpose is minus the field derivative minus divergence
(BB (2.3), p. 68). -/
theorem fieldTranspose_formula (V : (Fin n → ℝ) → (Fin n → ℝ))
    (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hV : DifferentiableAt ℝ V x) (hφ : DifferentiableAt ℝ φ x) :
    fieldTranspose V φ x = -fieldDerivative V φ x -
      φ x * Hormander.Interface.euclideanDivergence V x := by
  unfold fieldTranspose Hormander.Interface.euclideanDivergence fieldDerivative
  rw [fderiv_fun_smul hφ hV]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [differential_coordinates (fderiv ℝ φ x) (V x)]
  simp_rw [mul_comm (V x _) (fderiv ℝ φ x _)]
  ring

/-- First order classical product rule (BB p. 68). -/
theorem fieldDerivative_mul (V : (Fin n → ℝ) → (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (fun y => f y * g y) x =
      fieldDerivative V f x * g x + f x * fieldDerivative V g x := by
  simp [fieldDerivative, fderiv_fun_mul hf hg, mul_comm, add_comm]

/-- Transpose product rule (BB (2.2), p. 68). -/
theorem fieldTranspose_mul (V : (Fin n → ℝ) → (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hV : DifferentiableAt ℝ V x) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    fieldTranspose V (fun y => f y * g y) x =
      f x * fieldTranspose V g x - g x * fieldDerivative V f x := by
  rw [fieldTranspose_formula V _ x hV (hf.fun_mul hg),
    fieldTranspose_formula V g x hV hg, fieldDerivative_mul V f g x hf hg]
  ring

/-- Bundled test transpose agrees with the scalar transpose
(BB (2.2), p. 68). -/
theorem fieldTransposeTest_apply (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ) :
    fieldTransposeTest Ω V hV φ x = fieldTranspose V φ x := by
  have hd : ∀ j : Fin n, DifferentiableAt ℝ (fun y => φ y * V y j) x := by
    intro j
    exact (testMultiplierOn Ω (fun y => V y j)
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) φ).contDiff.differentiable
        (by simp) |>.differentiableAt
  unfold fieldTransposeTest fieldTranspose Hormander.Interface.euclideanDivergence
  simp only [neg_apply]
  congr 1
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ j : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (TestFunction.lineDerivCLM ℝ (Hormander.Interface.basisVec j)
    (testMultiplierOn Ω (fun y => V y j)
      ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) φ) :
        TestFunction Ω ℝ (⊤ : ℕ∞)) x = _
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  change lineDeriv ℝ (fun y => φ y * V y j) x _ = _
  rw [(hd j).lineDeriv_eq_fderiv]
  change fderiv ℝ (fun y => φ y * V y j) x _ = _
  change _ = fderiv ℝ (fun y j => φ y * V y j) x (Hormander.Interface.basisVec j) j
  rw [fderiv_pi hd]
  rfl

/-- Function coercion of the bundled transpose (BB (2.2), p. 68). -/
theorem fieldTransposeTest_coe (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (fieldTransposeTest Ω V hV φ : (Fin n → ℝ) → ℝ) = fieldTranspose V φ :=
  funext (fieldTransposeTest_apply Ω V hV φ)

/-- Scalar transpose never enlarges test support (BB (2.2), p. 68). -/
theorem tsupport_fieldTranspose_subset
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) :
    tsupport (fieldTranspose V φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hz : fderiv ℝ (fun y => φ y • V y) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => h
      ((tsupport_fderiv_subset ℝ).trans (tsupport_smul_subset_left φ V) ht))
  exact hx (by simp [fieldTranspose, Hormander.Interface.euclideanDivergence, hz])

/-- Word transposition reverses composition (BB p. 68). -/
theorem wordTransposeTest_apply (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (wordTransposeTest Ω X hX I φ : (Fin n → ℝ) → ℝ) = wordTranspose X I φ := by
  induction I generalizing φ with
  | nil => rfl
  | cons i I ih =>
    rw [wordTransposeTest, wordTranspose, ih]
    congr 1
    funext x
    exact fieldTransposeTest_apply Ω (X i) (hX i) φ x

/-- All word transposes preserve support (BB p. 68). -/
theorem tsupport_wordTranspose_subset
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (φ : (Fin n → ℝ) → ℝ) : tsupport (wordTranspose X I φ) ⊆ tsupport φ := by
  induction I generalizing φ with
  | nil => exact Subset.rfl
  | cons i I ih => exact (ih _).trans (tsupport_fieldTranspose_subset (X i) φ)

/-- Differentiating a smooth function along a smooth field preserves
smoothness on the open set (BB p. 68). -/
theorem contDiffOn_fieldDerivative (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative V f) (Ω : Set (Fin n → ℝ)) :=
  (hf.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply hV

end RothschildStein.S
