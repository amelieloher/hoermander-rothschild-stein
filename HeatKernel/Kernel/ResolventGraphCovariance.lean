-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.InverseResolventGraph

/-! # Resolvent covariance from operator graph covariance

Mapping the inverse-resolvent graph gives an intertwining relation for
the resolvents. Scaling the operator value gives the affine resolvent
parameter relation used for parabolic dilation.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- Scaling operator values under a linear map gives the affine resolvent parameter identity. -/
theorem resolvent_affine_intertwining_of_scaled_graph_map {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (R U : H →L[ℝ] H) (c : ℝ)
    (hmap : ∀ u g, InverseResolventGraph R u g →
      InverseResolventGraph R (U u) (c • U g)) :
    (R.comp U).comp (c • ContinuousLinearMap.id ℝ H + (1 - c) • R) = U.comp R := by
  ext f
  have h := (inverseResolventGraph_iff R (U (R f)) (c • U (f - R f))).mp
    (hmap (R f) (f - R f) ⟨f, rfl, rfl⟩)
  have heq : U (R f) + c • U (f - R f) = U (c • f + (1 - c) • R f) := by
    rw [map_add, map_smul, map_smul, map_sub, smul_sub, sub_smul, one_smul]
    abel
  rw [heq] at h
  exact h

end HeatKernel
