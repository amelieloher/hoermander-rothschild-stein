-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ScaledGraphFunctionalCalculus
public import HeatKernel.Kernel.HeatOperatorCovariance
public import HeatKernel.Semigroup.RealHeatOperators

/-! # Graph covariance for ambient and real heat operators

A unitary scaling of the operator graph rescales every nonnegative heat time.
A compatible real action inherits the same identity on an invariant closed subspace.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Scaled graph covariance gives conjugacy of the named heat operators, including at zero. -/
theorem conjStarAlgEquiv_heatOperator_of_scaled_graph_map
    (e : E ≃ₗᵢ[ℂ] E) (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hσ : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) {c : ℝ≥0} (hc : 0 < c)
    (hmap : ∀ u g, R (u + g) = u → R (e u + (c : ℝ) • e g) = e u) (t : ℝ≥0) :
    e.symm.conjStarAlgEquiv (heatOperator R t) = heatOperator R (c * t) :=
  conjStarAlgEquiv_heatOperator_of_resolvent_scale e R hR hσ hc
    (conjStarAlgEquiv_resolvent_of_scaled_graph_map e R hR hσ (NNReal.coe_pos.mpr hc) hmap) t

/-- A unitary scaling of the graph intertwines the heat operators with rescaled time. -/
theorem heatOperator_apply_unitary_of_scaled_graph_map
    (e : E ≃ₗᵢ[ℂ] E) (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hσ : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1) {c : ℝ≥0} (hc : 0 < c)
    (hmap : ∀ u g, R (u + g) = u → R (e u + (c : ℝ) • e g) = e u)
    (t : ℝ≥0) (v : E) :
    heatOperator R t (e v) = e (heatOperator R (c * t) v) := by
  have h := congrArg (fun T : E →L[ℂ] E => T v)
    (conjStarAlgEquiv_heatOperator_of_scaled_graph_map e R hR hσ hc hmap t)
  change e.symm (heatOperator R t (e v)) = heatOperator R (c * t) v at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using congrArg e h

end HeatKernel
