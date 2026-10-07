-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Decomposition

@[expose] public section

noncomputable section

open SchwartzMap

namespace Hormander.C

open Hormander.B

variable {N : ℕ}

/-- Real Schwartz product `f * g`. -/
def schwartzMul (f g : SchwartzMap (Carrier N) ℝ) : SchwartzMap (Carrier N) ℝ :=
  SchwartzMap.smulLeftCLM ℝ (f : Carrier N → ℝ) g

theorem schwartzMul_apply (f g : SchwartzMap (Carrier N) ℝ) (x : Carrier N) :
    schwartzMul f g x = f x * g x := by
  unfold schwartzMul
  rw [SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth]
  rfl

/-- The real coordinate derivative `∂ᵢ` of a real Schwartz function. -/
def realDeriv (i : Fin N) (f : SchwartzMap (Carrier N) ℝ) : SchwartzMap (Carrier N) ℝ :=
  LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f

theorem realDeriv_apply (i : Fin N) (f : SchwartzMap (Carrier N) ℝ) (x : Carrier N) :
    realDeriv i f x = fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) :=
  SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ x

/-- The Lie bracket of two real Schwartz vector fields. -/
def bracketField (X Y : RealSchwartzVectorField N) : RealSchwartzVectorField N := fun m =>
  ∑ i : Fin N, (schwartzMul (X i) (realDeriv i (Y m)) - schwartzMul (Y i) (realDeriv i (X m)))

theorem bracketField_apply (X Y : RealSchwartzVectorField N) (m : Fin N) (x : Carrier N) :
    bracketField X Y m x = ∑ i : Fin N, (X i x * fderiv ℝ (Y m) x (EuclideanSpace.single i 1) -
      Y i x * fderiv ℝ (X m) x (EuclideanSpace.single i 1)) := by
  unfold bracketField
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_apply, schwartzMul_apply, schwartzMul_apply, realDeriv_apply, realDeriv_apply]

theorem coordinateDerivative_complexify_apply (a : SchwartzMap (Carrier N) ℝ) (i : Fin N)
    (x : Carrier N) :
    coordinateDerivative i (complexifyRealSchwartz a) x =
      ((fderiv ℝ a x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ) := complexify_deriv a i x

/-- `X u (x)` as a finite sum of derivative values. -/
theorem vectorField_apply' (X : RealSchwartzVectorField N) (u : TestFunction N) (x : Carrier N) :
    vectorFieldOperator X u x = ∑ i : Fin N, (X i x : ℂ) * coordinateDerivative i u x :=
  vectorFieldOperator_apply X u x

theorem coordinateDerivative_vectorField_apply (Y : RealSchwartzVectorField N) (u : TestFunction N)
    (i : Fin N) (x : Carrier N) :
    coordinateDerivative i (vectorFieldOperator Y u) x =
      ∑ m : Fin N, ((fderiv ℝ (Y m) x (EuclideanSpace.single i 1) : ℝ) : ℂ) *
          coordinateDerivative m u x +
        ∑ m : Fin N, (Y m x : ℂ) * coordinateDerivative i (coordinateDerivative m u) x := by
  have hV : vectorFieldOperator Y u = ∑ m : Fin N, multiplierOperator (complexifyRealSchwartz (Y m))
      (coordinateDerivative m u) := by
    unfold vectorFieldOperator
    rw [LinearMap.sum_apply]
    rfl
  rw [hV, map_sum, sum_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coordinateDerivative_mul_apply, coordinateDerivative_complexify_apply,
    complexifyRealSchwartz_apply]

/-- The commutator of two real Schwartz vector fields is the vector field of their Lie bracket. -/
theorem operatorComm_vectorField_vectorField (X Y : RealSchwartzVectorField N) :
    operatorComm (vectorFieldOperator X) (vectorFieldOperator Y) =
      vectorFieldOperator (bracketField X Y) := by
  ext u x
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.comp_apply, sub_apply]
  rw [vectorField_apply' X (vectorFieldOperator Y u) x, vectorField_apply' Y (vectorFieldOperator X u) x,
    vectorField_apply']
  simp only [coordinateDerivative_vectorField_apply, bracketField_apply]
  have hcomm : ∀ i m, coordinateDerivative i (coordinateDerivative m u) x =
      coordinateDerivative m (coordinateDerivative i u) x := fun i m => by
    have := LinearMap.congr_fun (coordinateDerivative_comp_comm i m) u
    exact congrArg (fun w : TestFunction N => w x) this
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, push_cast, Finset.sum_sub_distrib]
  have h2 : ∑ x_1, ∑ i, (Y x_1 x : ℂ) * ((X i x : ℂ) * coordinateDerivative x_1 (coordinateDerivative i u) x) =
      ∑ x_1, ∑ i, (X x_1 x : ℂ) * ((Y i x : ℂ) * coordinateDerivative x_1 (coordinateDerivative i u) x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hcomm]; ring
  rw [h2, add_sub_add_right_eq_sub]
  simp only [sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => (X a x : ℂ) * (((fderiv ℝ (Y b) x (EuclideanSpace.single a 1) : ℝ) : ℂ) * coordinateDerivative b u x)),
    Finset.sum_comm (f := fun a b => (Y a x : ℂ) * (((fderiv ℝ (X b) x (EuclideanSpace.single a 1) : ℝ) : ℂ) * coordinateDerivative b u x))]
  congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;> ring

/-- The right-nested bracket field `[X_{i₁}, [X_{i₂}, … X_{i_ℓ}]]` of a nonempty word. -/
def wordField {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N) :
    List (Fin (k + 1)) → RealSchwartzVectorField N
  | [] => 0
  | [j] => X j
  | j :: i :: I => bracketField (X j) (wordField X (i :: I))

theorem vectorField_wordField_cons {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (j : Fin (k + 1)) {I : List (Fin (k + 1))} (hI : I ≠ []) :
    vectorFieldOperator (wordField X (j :: I)) =
      operatorComm (vectorFieldOperator (X j)) (vectorFieldOperator (wordField X I)) := by
  cases I with
  | nil => exact absurd rfl hI
  | cons i I =>
    rw [operatorComm_vectorField_vectorField]
    rfl

end Hormander.C
