-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmoothLocalChartInverse
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- The actual nonzero Jacobian supplies an open local chart at
each point. Its forward map is the given exponential chart, with no
global inverse or covering assumption (BB Prop 9.52, p. 448). -/
theorem exists_actual_chart_local_homeomorph {n : ℕ}
    (F : (Fin n → ℝ) → (Fin n → ℝ)) {u : Fin n → ℝ}
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F u)
    (hdet : Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ),
      u ∈ e.source ∧ F = e := by
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
  exact ⟨hF.toOpenPartialHomeomorph F hd hn,
    hF.mem_toOpenPartialHomeomorph_source hd hn, (hF.toOpenPartialHomeomorph_coe hd hn).symm⟩

/-- The proved Jacobian bound on an open box makes the actual
chart a local homeomorphism throughout that box, as required by lift
uniqueness and continuation (BB Prop 9.52, pp. 448–449). -/
theorem isLocalHomeomorphOn_of_actual_jacobian {n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hdet : ∀ u ∈ U, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0) :
    IsLocalHomeomorphOn F U := by
  intro u hu
  exact exists_actual_chart_local_homeomorph F (hF.contDiffAt (hU.mem_nhds hu)) (hdet u hu)

end RothschildStein.G4
