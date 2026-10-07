-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

namespace Hormander.C

/-- The coefficient matrix whose columns are the selected frame
vectors. -/
def frameMatrix {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ := fun i a => (EuclideanSpace.proj (𝕜 := ℝ) i) (v a)

/-- The coefficient matrix of a frame field at a point. -/
def frameMatrixAt {N : ℕ} (V : Fin N → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  frameMatrix (fun a => V a x)

/-- The row of the inverse frame matrix giving a coordinate
vector in the selected frame. -/
def frameInverseCoefficient {N : ℕ}
    (V : Fin N → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (j a : Fin N) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (frameMatrixAt V x)⁻¹ a j

/-- The selected vectors are linearly independent exactly when their coefficient
matrix has nonzero determinant. -/
theorem frameMatrix_det_ne_zero_iff {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) :
    (frameMatrix v).det ≠ 0 ↔ LinearIndependent ℝ v := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (frameMatrix v).col =
      (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).toLinearMap ∘ v := by
    funext a i
    rfl
  rw [hcol]
  exact LinearMap.linearIndependent_iff _
    (LinearEquiv.ker (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)))

/-- Smooth frame fields give smooth entries of the inverse
coefficient matrix wherever its determinant is nonzero. -/
theorem frame_inverse_coefficient_contDiffOn {N : ℕ}
    (V : Fin N → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (hV : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (V a)) {U : Set (EuclideanSpace ℝ (Fin N))}
    (hdet : ∀ x ∈ U, (frameMatrixAt V x).det ≠ 0) (j a : Fin N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => frameInverseCoefficient V j a x) U := by
  have hframeEntry (i b : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => frameMatrixAt V x i b) U := by
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (EuclideanSpace.proj (𝕜 := ℝ) i) (V b x)) U
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn (hV b).contDiffOn
  have hdetSmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => (frameMatrixAt V x).det) U := by
    simp_rw [Matrix.det_apply']
    fun_prop
  have hupdatedEntry (i b : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ((frameMatrixAt V x).updateRow j (Pi.single a 1)) i b) U := by
    by_cases hij : i = j
    · simp [Matrix.updateRow_apply, hij, Pi.single_apply]
      fun_prop
    · simpa [Matrix.updateRow_apply, hij, Pi.single_apply] using hframeEntry i b
  have hAdjEntry : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => Matrix.adjugate (frameMatrixAt V x) a j) U := by
    have heq : (fun x => Matrix.adjugate (frameMatrixAt V x) a j) =
        fun x => ((frameMatrixAt V x).updateRow j (Pi.single a 1)).det := by
      funext x
      exact Matrix.adjugate_apply (frameMatrixAt V x) a j
    rw [heq]
    simp_rw [Matrix.det_apply']
    fun_prop
  have hdetInv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ((frameMatrixAt V x).det)⁻¹) U :=
    hdetSmooth.inv fun x hx => hdet x hx
  have hmul : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ((frameMatrixAt V x).det)⁻¹ * (frameMatrixAt V x).adjugate a j) U :=
    hdetInv.mul hAdjEntry
  have heq : (fun x => frameInverseCoefficient V j a x) =
      fun x => ((frameMatrixAt V x).det)⁻¹ * (frameMatrixAt V x).adjugate a j := by
    funext x
    simp [frameInverseCoefficient, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  rw [heq]
  exact hmul

/-- The inverse matrix coefficients express each coordinate
vector in the selected frame. -/
theorem frame_inverse_coordinate_identity {N : ℕ}
    (v : Fin N → EuclideanSpace ℝ (Fin N))
    (hdet : (frameMatrix v).det ≠ 0) (i j : Fin N) :
    ∑ a : Fin N, ((frameMatrix v)⁻¹ a j) * v a i = if i = j then 1 else 0 := by
  let M := frameMatrix v
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hentry := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) hmul
  simpa [M, frameMatrix, Matrix.mul_apply, Matrix.one_apply, mul_comm] using hentry

/-- A continuous nonvanishing determinant has a uniform positive
lower bound in absolute value on a compact set. -/
theorem exists_positive_abs_lower_bound_on_compact {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) (f : E → ℝ) (hf : Continuous f)
    (hne : ∀ x ∈ K, f x ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K, d ≤ |f x| := by
  have habs : Continuous fun x => |f x| := hf.abs
  have hpositive : ∀ x ∈ K, 0 < |f x| := fun x hx => abs_pos.mpr (hne x hx)
  obtain ⟨d, hd, hbound⟩ := hK.exists_forall_le' habs.continuousOn hpositive
  exact ⟨d, hd, hbound⟩

end Hormander.C
