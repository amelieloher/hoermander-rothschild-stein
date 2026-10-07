-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalJacobianNonzero
public import RothschildStein.L1.JointPullbackFields
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The finite determinant is smooth whenever all actual matrix entries are. -/
theorem matrixDet_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (U : Set E) (A : E → Matrix (Fin N) (Fin N) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun q => A q i j) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => (A q).det) U := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiffOn.sum
  intro σ _
  exact contDiffOn_const.mul (contDiffOn_prod (fun j _ => hA (σ j) j))

namespace CanonicalFrameChartData
variable {N : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

end CanonicalFrameChartData
end RothschildStein.L1
