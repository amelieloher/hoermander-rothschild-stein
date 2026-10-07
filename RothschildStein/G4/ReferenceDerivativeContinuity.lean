-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RothschildStein.G4

/-- The derivative normalized by its own inverse is the identity
at the reference point (BB (9.55), p. 453). -/
theorem normalized_reference_derivative_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E ≃L[ℝ] F) :
    (L.symm : F →L[ℝ] E).comp (L : E →L[ℝ] F) - ContinuousLinearMap.id ℝ E = 0 := by
  ext x
  change L.symm (L x) - x = 0
  simp only [ContinuousLinearEquiv.symm_apply_apply, sub_self]

/-- Continuity of the actual derivative gives continuity of its
normalized error norm (BB (9.55), p. 453). -/
theorem normalized_reference_error_continuousAt
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : P → (E →L[ℝ] F)) (p₀ : P) (L : E ≃L[ℝ] F)
    (hT : ContinuousAt T p₀) :
    ContinuousAt (fun p => ‖(L.symm : F →L[ℝ] E).comp (T p) -
      ContinuousLinearMap.id ℝ E‖) p₀ := by
  have hleft : ContinuousAt (fun _ : P => (L.symm : F →L[ℝ] E)) p₀ := continuousAt_const
  have hid : ContinuousAt (fun _ : P => ContinuousLinearMap.id ℝ E) p₀ := continuousAt_const
  have hcomp : ContinuousAt (fun p => (L.symm : F →L[ℝ] E).comp (T p)) p₀ :=
    hleft.clm_comp hT
  exact (hcomp.sub hid).norm

/-- The normalized error is less than one half in a neighborhood
of an invertible reference derivative (BB (9.55), p. 453). -/
theorem eventually_normalized_reference_error_lt_half
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : P → (E →L[ℝ] F)) (p₀ : P) (L : E ≃L[ℝ] F)
    (hT : ContinuousAt T p₀) (hbase : T p₀ = (L : E →L[ℝ] F)) :
    ∀ᶠ p in 𝓝 p₀, ‖(L.symm : F →L[ℝ] E).comp (T p) -
      ContinuousLinearMap.id ℝ E‖ < (1 / 2 : ℝ) := by
  have hnorm := normalized_reference_error_continuousAt T p₀ L hT
  have hzero : ‖(L.symm : F →L[ℝ] E).comp (T p₀) - ContinuousLinearMap.id ℝ E‖ = 0 := by
    rw [hbase, normalized_reference_derivative_zero, norm_zero]
  exact hnorm.eventually_lt continuousAt_const (by rw [hzero]; norm_num)

end RothschildStein.G4
