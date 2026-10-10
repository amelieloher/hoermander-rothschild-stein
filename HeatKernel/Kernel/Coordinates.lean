-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Hormander.Interface.EuclideanDivergence

/-! # Coordinates for time and spatial blocks

Splitting finite coordinate sets gives continuous linear equivalences for spacetime and
for two spatial blocks. Coordinate inclusions preserve the divergence of differentiable fields.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open Hormander.Interface

/-- Split a finite coordinate vector into two consecutive blocks. -/
def splitCoordinates (m n : ℕ) :
    (Fin (m + n) → ℝ) ≃L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (m + n) => ℝ)
    finSumFinEquiv).symm.trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin m) (Fin n) (fun _ => ℝ))

/-- Separate the time coordinate from a spatial vector. -/
def timeSpaceCoordinates (n : ℕ) :
    (Fin (1 + n) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  (splitCoordinates 1 n).trans
    ((ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ _))

/-- Separate time and two consecutive spatial blocks. -/
def timeTwoSpaceCoordinates (n : ℕ) :
    (Fin (1 + (n + n)) → ℝ) ≃L[ℝ] ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (timeSpaceCoordinates (n + n)).trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (splitCoordinates n n))

@[simp] theorem timeSpaceCoordinates_fst (n : ℕ) (x : Fin (1 + n) → ℝ) :
    (timeSpaceCoordinates n x).1 = x 0 := rfl

/-- Positive time is an open set in the coordinate vector space. -/
theorem isOpen_positive_time (n : ℕ) :
    IsOpen {x : Fin (1 + n) → ℝ | 0 < x 0} :=
  isOpen_lt continuous_const (continuous_apply 0)

/-- Projection to the first coordinate block. -/
def leftCoordinateProjection (m n : ℕ) :
    (Fin (m + n) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (splitCoordinates m n).toContinuousLinearMap

/-- Projection to the second coordinate block. -/
def rightCoordinateProjection (m n : ℕ) :
    (Fin (m + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (ContinuousLinearMap.snd ℝ _ _).comp (splitCoordinates m n).toContinuousLinearMap

/-- Inclusion into the first coordinate block, with zero second block. -/
def leftCoordinateInclusion (m n : ℕ) :
    (Fin m → ℝ) →L[ℝ] (Fin (m + n) → ℝ) :=
  (splitCoordinates m n).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

/-- Inclusion into the second coordinate block, with zero first block. -/
def rightCoordinateInclusion (m n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (m + n) → ℝ) :=
  (splitCoordinates m n).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)

@[simp] theorem leftCoordinateProjection_apply (m n : ℕ) (x : Fin (m + n) → ℝ)
    (i : Fin m) : leftCoordinateProjection m n x i = x (Fin.castAdd n i) := rfl

@[simp] theorem rightCoordinateProjection_apply (m n : ℕ) (x : Fin (m + n) → ℝ)
    (i : Fin n) : rightCoordinateProjection m n x i = x (Fin.natAdd m i) := rfl

@[simp] theorem leftCoordinateInclusion_castAdd (m n : ℕ) (x : Fin m → ℝ)
    (i : Fin m) : leftCoordinateInclusion m n x (Fin.castAdd n i) = x i := by
  change (splitCoordinates m n ((splitCoordinates m n).symm (x, 0))).1 i = x i
  simp only [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem leftCoordinateInclusion_natAdd (m n : ℕ) (x : Fin m → ℝ)
    (i : Fin n) : leftCoordinateInclusion m n x (Fin.natAdd m i) = 0 := by
  change (splitCoordinates m n ((splitCoordinates m n).symm (x, 0))).2 i = 0
  simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.zero_apply]

@[simp] theorem rightCoordinateInclusion_castAdd (m n : ℕ) (x : Fin n → ℝ)
    (i : Fin m) : rightCoordinateInclusion m n x (Fin.castAdd n i) = 0 := by
  change (splitCoordinates m n ((splitCoordinates m n).symm (0, x))).1 i = 0
  simp only [ContinuousLinearEquiv.apply_symm_apply, Pi.zero_apply]

@[simp] theorem rightCoordinateInclusion_natAdd (m n : ℕ) (x : Fin n → ℝ)
    (i : Fin n) : rightCoordinateInclusion m n x (Fin.natAdd m i) = x i := by
  change (splitCoordinates m n ((splitCoordinates m n).symm (0, x))).2 i = x i
  simp only [ContinuousLinearEquiv.apply_symm_apply]

@[simp] theorem leftCoordinateProjection_basisVec_castAdd (m n : ℕ) (i : Fin m) :
    leftCoordinateProjection m n (basisVec (Fin.castAdd n i)) = basisVec i := by
  ext j
  simp [basisVec, Pi.single_apply, Fin.castAdd_inj]

@[simp] theorem leftCoordinateProjection_basisVec_natAdd (m n : ℕ) (i : Fin n) :
    leftCoordinateProjection m n (basisVec (Fin.natAdd m i)) = 0 := by
  ext j
  simp [basisVec, Pi.single_apply, Fin.ext_iff]
  omega

@[simp] theorem rightCoordinateProjection_basisVec_castAdd (m n : ℕ) (i : Fin m) :
    rightCoordinateProjection m n (basisVec (Fin.castAdd n i)) = 0 := by
  ext j
  simp [basisVec, Pi.single_apply, Fin.ext_iff]
  omega

@[simp] theorem rightCoordinateProjection_basisVec_natAdd (m n : ℕ) (i : Fin n) :
    rightCoordinateProjection m n (basisVec (Fin.natAdd m i)) = basisVec i := by
  ext j
  simp [basisVec, Pi.single_apply, Fin.natAdd_inj]

/-- Lift a field to the first spatial block. -/
def liftLeftField {m : ℕ} (n : ℕ) (X : (Fin m → ℝ) → Fin m → ℝ) :
    (Fin (m + n) → ℝ) → Fin (m + n) → ℝ :=
  fun x => leftCoordinateInclusion m n (X (leftCoordinateProjection m n x))

/-- Lift a field to the second spatial block. -/
def liftRightField (m : ℕ) {n : ℕ} (X : (Fin n → ℝ) → Fin n → ℝ) :
    (Fin (m + n) → ℝ) → Fin (m + n) → ℝ :=
  fun x => rightCoordinateInclusion m n (X (rightCoordinateProjection m n x))

/-- Lifting a smooth field to the first block gives a smooth field. -/
theorem _root_.ContDiff.liftLeftField {m : ℕ} (n : ℕ)
    {X : (Fin m → ℝ) → Fin m → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (liftLeftField n X) :=
  (leftCoordinateInclusion m n).contDiff.comp
    (hX.comp (leftCoordinateProjection m n).contDiff)

/-- Lifting a smooth field to the second block gives a smooth field. -/
theorem _root_.ContDiff.liftRightField (m : ℕ) {n : ℕ}
    {X : (Fin n → ℝ) → Fin n → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (liftRightField m X) :=
  (rightCoordinateInclusion m n).contDiff.comp
    (hX.comp (rightCoordinateProjection m n).contDiff)

/-- Lifting a differentiable field to the first block preserves its divergence. -/
theorem euclideanDivergence_liftLeftField {m : ℕ} (n : ℕ)
    (X : (Fin m → ℝ) → Fin m → ℝ) (x : Fin (m + n) → ℝ)
    (hX : DifferentiableAt ℝ X (leftCoordinateProjection m n x)) :
    euclideanDivergence (liftLeftField n X) x =
      euclideanDivergence X (leftCoordinateProjection m n x) := by
  have hd := (leftCoordinateInclusion m n).hasFDerivAt.comp x
    (hX.hasFDerivAt.comp x (leftCoordinateProjection m n).hasFDerivAt)
  unfold euclideanDivergence
  change (∑ i, (fderiv ℝ
    ((leftCoordinateInclusion m n) ∘ X ∘ (leftCoordinateProjection m n)) x
      (basisVec i)) i) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_add]
  simp

/-- Lifting a differentiable field to the second block preserves its divergence. -/
theorem euclideanDivergence_liftRightField (m : ℕ) {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (x : Fin (m + n) → ℝ)
    (hX : DifferentiableAt ℝ X (rightCoordinateProjection m n x)) :
    euclideanDivergence (liftRightField m X) x =
      euclideanDivergence X (rightCoordinateProjection m n x) := by
  have hd := (rightCoordinateInclusion m n).hasFDerivAt.comp x
    (hX.hasFDerivAt.comp x (rightCoordinateProjection m n).hasFDerivAt)
  unfold euclideanDivergence
  change (∑ i, (fderiv ℝ
    ((rightCoordinateInclusion m n) ∘ X ∘ (rightCoordinateProjection m n)) x
      (basisVec i)) i) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_add]
  simp

end HeatKernel
