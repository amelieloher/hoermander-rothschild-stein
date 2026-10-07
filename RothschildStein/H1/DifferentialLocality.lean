-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DifferentialTranspose
public import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

private theorem coordinateFold_eventuallyEq (l : List (Fin N))
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) f =ᶠ[𝓝 x]
      l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) g := by
  induction l with
  | nil => exact he
  | cons j l ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A => A (Hormander.Interface.basisVec j)) hy

/-- Finite coordinate derivatives depend only on the germ. -/
theorem euclideanPartial_eventuallyEq (a : Fin N → ℕ)
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    euclideanPartial a f =ᶠ[𝓝 x] euclideanPartial a g :=
  coordinateFold_eventuallyEq _ he

/-- The smooth differential operator is local. -/
theorem differentialOperator_germ_eq (P : SmoothDifferentialOperator N)
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    P.apply f x = P.apply g x := by
  unfold SmoothDifferentialOperator.apply
  apply Finset.sum_congr rfl
  intro a _
  rw [(euclideanPartial_eventuallyEq a he).eq_of_nhds]

/-- The formal transpose is local, including on functions
that are constant near the origin or outside a compact set. -/
theorem differentialTranspose_germ_eq (P : SmoothDifferentialOperator N)
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    G2.differentialTranspose P f x = G2.differentialTranspose P g x := by
  unfold G2.differentialTranspose
  apply Finset.sum_congr rfl
  intro a _
  have hm : (fun y => P.coefficient a y * f y) =ᶠ[𝓝 x]
      fun y => P.coefficient a y * g y := by
    filter_upwards [he] with y hy
    rw [hy]
  rw [(euclideanPartial_eventuallyEq a hm).eq_of_nhds]

end RothschildStein.H1
