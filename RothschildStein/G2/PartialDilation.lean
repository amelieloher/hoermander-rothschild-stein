-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ExponentialTests
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The dilation differential on a coordinate vector. -/
theorem dilationDifferential_basis (t : ℝ) (j : Fin N) :
    dilationDifferential G t (Hormander.Interface.basisVec j) =
      t ^ G.weight j • Hormander.Interface.basisVec j := by
  classical
  ext k
  simp [dilationDifferential, Hormander.Interface.basisVec, Pi.single_apply]
  split_ifs <;> simp_all

/-- Each coordinate derivative has the coordinate dilation weight. -/
theorem coordinateDerivative_dilate (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (j : Fin N) (x : Fin N → ℝ) :
    fderiv ℝ (f ∘ G.dilate t) x (Hormander.Interface.basisVec j) =
      t ^ G.weight j * fderiv ℝ f (G.dilate t x) (Hormander.Interface.basisVec j) := by
  rw [fderiv_comp x (hf.differentiable (by simp)).differentiableAt
    (hasFDerivAt_dilate G t x).differentiableAt, (hasFDerivAt_dilate G t x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, dilationDifferential_basis, map_smul, smul_eq_mul]

/-- Coordinate words transform by the product of their coordinate weights. -/
theorem coordinateWord_dilate (l : List (Fin N)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    l.foldr (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) (f ∘ G.dilate t) =
      fun x => (l.map (fun j => t ^ G.weight j)).prod *
        (l.foldr (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f) (G.dilate t x) := by
  induction l with
  | nil => simp [Function.comp_def]
  | cons j l ih =>
    rw [List.foldr_cons, ih]
    let F := l.foldr (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j)) f
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
      have hs := (l.foldr coordinateAction ⟨f, hf⟩).property
      simpa only [coordinateWord_coe] using hs
    funext x
    change fderiv ℝ (fun y => (l.map (fun j => t ^ G.weight j)).prod *
      (F ∘ G.dilate t) y) x (Hormander.Interface.basisVec j) = _
    rw [fderiv_const_mul ((hF.comp (contDiff_dilate G t)).differentiable (by simp)).differentiableAt]
    simp only [smul_apply, smul_eq_mul]
    rw [coordinateDerivative_dilate G F hF t j x]
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    ring

/-- Multi-index chain rule for diagonal dilations
(BB p. 107; used in the general coefficient criterion). -/
theorem euclideanPartial_dilate (a : Fin N → ℕ) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (x : Fin N → ℝ) :
    euclideanPartial a (f ∘ G.dilate t) x =
      t ^ (∑ j, G.weight j * a j) * euclideanPartial a f (G.dilate t x) := by
  change ((coordinateWord a).foldr _ (f ∘ G.dilate t)) x = _
  rw [coordinateWord_dilate G _ f hf, coordinateWord_product]
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, euclideanPartial, coordinateWord]

end RothschildStein.G2
