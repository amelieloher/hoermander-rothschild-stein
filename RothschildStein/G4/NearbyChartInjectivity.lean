-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ConvexChartInjectivity
public import Mathlib.Analysis.Normed.Module.Convex
public import RothschildStein.G4.ReferenceDerivativeContinuity
public import RothschildStein.G4.ProductBallNeighborhood

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology

namespace RothschildStein.G4

/-- Joint derivative continuity gives one convex spatial ball
and one parameter neighborhood on which every chart is injective. The
family parameter only has a topology (BB (9.55), p. 453). -/
theorem exists_nearby_injective_ball_of_joint_derivative_continuity
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → E → F) (x₀ : E) (p₀ : P) (L : E ≃L[ℝ] F)
    (hlocal : ∀ᶠ q : E × P in 𝓝 (x₀, p₀), DifferentiableAt ℝ (f q.2) q.1)
    (hder : ContinuousAt (fun q : E × P => fderiv ℝ (f q.2) q.1) (x₀, p₀))
    (hbase : fderiv ℝ (f p₀) x₀ = (L : E →L[ℝ] F)) :
    ∃ r : ℝ, 0 < r ∧ ∃ V : Set P, V ∈ 𝓝 p₀ ∧
      ∀ p ∈ V, InjOn (f p) (ball x₀ r) := by
  have hsmall := eventually_normalized_reference_error_lt_half
    (fun q : E × P => fderiv ℝ (f q.2) q.1) (x₀, p₀) L hder hbase
  let A := fun q : E × P => DifferentiableAt ℝ (f q.2) q.1 ∧
    ‖(L.symm : F →L[ℝ] E).comp (fderiv ℝ (f q.2) q.1) -
      ContinuousLinearMap.id ℝ E‖ < (1 / 2 : ℝ)
  have hgood : ∀ᶠ q in 𝓝 (x₀, p₀), A q := hlocal.and hsmall
  obtain ⟨r, hr, V, hV, hUV⟩ := exists_product_ball_of_eventually A x₀ p₀ hgood
  refine ⟨r, hr, V, hV, ?_⟩
  intro p hp
  exact convex_injOn_of_normalized_derivative_bound (convex_ball x₀ r) (f p) L
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun x hx => (hUV x hx p hp).1)
    (fun x hx => (hUV x hx p hp).2.le)

end RothschildStein.G4
