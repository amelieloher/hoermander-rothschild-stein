-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualFrameInverseColumns
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RothschildStein.G4

/-- A smooth actual chart with nonzero coordinate Jacobian has a
smooth local inverse and both local inverse identities. This uses the
proved actual derivative matrix, with no quantitative inverse existence
premise (BB Proposition 9.50, pp. 445–446). -/
theorem exists_smooth_local_chart_inverse {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {u : Fin n → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F u)
    (hdet : Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) :
    ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiffAt ℝ (⊤ : ℕ∞) Ψ (F u) ∧ Ψ (F u) = u ∧
      ((fun z => F (Ψ z)) =ᶠ[𝓝 (F u)] (fun z => z)) ∧
      ((fun a => Ψ (F a)) =ᶠ[𝓝 u] (fun a => a)) := by
  have hinj : Function.Injective (fderiv ℝ F u) := by
    have hunit : IsUnit (coordinateDerivativeMatrix (fderiv ℝ F u)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    intro a b hab
    apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa only [coordinateDerivativeMatrix_mulVec] using hab
  let L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ F u).toLinearMap hinj).toContinuousLinearEquiv
  have hL : (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ F u := by
    ext a; rfl
  have hd : HasFDerivAt F (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) u := by
    rw [hL]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hF.localInverse hd hn, hF.to_localInverse hd hn,
    hF.localInverse_apply_image hd hn, ?_, ?_⟩
  · exact (hF.hasStrictFDerivAt' hd hn).eventually_right_inverse
  · exact (hF.hasStrictFDerivAt' hd hn).eventually_left_inverse

end RothschildStein.G4
