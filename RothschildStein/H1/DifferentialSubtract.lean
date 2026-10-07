-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DifferentialScalar
public import RothschildStein.G2.CoordinateIntegration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ}

private theorem coordinateFold_smooth (l : List (Fin N))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (l.foldr
      (fun j h x => fderiv ℝ h x (Hormander.Interface.basisVec j)) f) := by
  induction l with
  | nil => exact hf
  | cons j l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

private theorem coordinateFold_sub (l : List (Fin N))
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    l.foldr (fun j h x => fderiv ℝ h x (Hormander.Interface.basisVec j)) (fun x => f x - g x) =
      fun x => l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) f x -
        l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) g x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    change fderiv ℝ (l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) f -
      l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) g) x
      (Hormander.Interface.basisVec j) = _
    rw [fderiv_sub ((coordinateFold_smooth l hf).differentiable (by simp)).differentiableAt
      ((coordinateFold_smooth l hg).differentiable (by simp)).differentiableAt]
    rfl

/-- Multi-index derivatives distribute over a smooth cutoff difference. -/
theorem euclideanPartial_sub {f g : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (a : Fin N → ℕ) :
    euclideanPartial a (fun x => f x - g x) = fun x => euclideanPartial a f x - euclideanPartial a g x :=
  coordinateFold_sub _ hf hg

/-- Step 2: the formal transpose distributes over smooth cutoff differences. -/
theorem differentialTranspose_sub (P : SmoothDifferentialOperator N)
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    G2.differentialTranspose P (fun x => f x - g x) =
      fun x => G2.differentialTranspose P f x - G2.differentialTranspose P g x := by
  funext x
  simp only [G2.differentialTranspose, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have he : (fun y => P.coefficient a y * (f y - g y)) =
      fun y => P.coefficient a y * f y - P.coefficient a y * g y := by funext y; ring
  rw [he, euclideanPartial_sub ((P.smooth_coefficient a ha).mul hf)
    ((P.smooth_coefficient a ha).mul hg)]
  ring

end RothschildStein.H1
