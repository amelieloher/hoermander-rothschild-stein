-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Drift

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.C
open Hormander.B
variable {N k : ℕ}

theorem fderiv_apply_eq_sum (f : Carrier N → ℂ) (y v : Carrier N) (_hf : DifferentiableAt ℝ f y) :
    fderiv ℝ f y v = ∑ j : Fin N, ((v j : ℝ) : ℂ) * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ)) := by
  have hv : v = ∑ j : Fin N, (v j) • EuclideanSpace.single j (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Complex.real_smul]

/-- A Schwartz field representing a pointwise field `X` acts as the directional derivative. -/
theorem vectorFieldOperator_eq_fderiv (Xs : RealSchwartzVectorField N) (X : Carrier N → Carrier N)
    (hXs : ∀ x j, Xs j x = X x j) (u : TestFunction N) (y : Carrier N) :
    vectorFieldOperator Xs u y = fderiv ℝ (u : Carrier N → ℂ) y (X y) := by
  rw [vectorFieldOperator_apply, fderiv_apply_eq_sum _ _ _ u.differentiableAt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hXs]
  have : coordinateDerivative j u y = fderiv ℝ (u : Carrier N → ℂ) y (EuclideanSpace.single j (1 : ℝ)) :=
    SchwartzMap.lineDerivOp_apply_eq_fderiv _ u y
  rw [this]

/-- The Schwartz realization of `L̃` agrees with the displayed pointwise integrand. -/
theorem diffusionOperator_apply_pointwise {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N)
    (X : Fin (k + 1) → Carrier N → Carrier N) (hXs : ∀ i x j, Xs i j x = X i x j)
    (cs : SchwartzMap (Carrier N) ℝ) (c : Carrier N → ℝ) (hc : ∀ x, cs x = c x)
    (u : TestFunction N) (x : Carrier N) :
    diffusionOperator Xs cs u x =
      (∑ i : Fin k, fderiv ℝ (fun y => fderiv ℝ (u : Carrier N → ℂ) y (X i.succ y)) x (X i.succ x)) +
        fderiv ℝ (u : Carrier N → ℂ) x (X 0 x) + (c x : ℂ) * u x := by
  have hfun : ∀ i, (⇑(vectorFieldOperator (Xs i) u) : Carrier N → ℂ) =
      fun y => fderiv ℝ (u : Carrier N → ℂ) y (X i y) := fun i => by
    funext y; exact vectorFieldOperator_eq_fderiv (Xs i) (X i) (hXs i) u y
  unfold diffusionOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply, add_apply, sum_apply]
  have hrm : realMultiplierOperator cs u x = (c x : ℂ) * u x := by
    unfold realMultiplierOperator
    rw [multiplierOperator_apply, complexifyRealSchwartz_apply, hc]
  rw [hrm, vectorFieldOperator_eq_fderiv (Xs 0) (X 0) (hXs 0)]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vectorFieldOperator_eq_fderiv (Xs i.succ) (X i.succ) (hXs i.succ) (vectorFieldOperator (Xs i.succ) u) x,
    hfun i.succ]

end Hormander.C
