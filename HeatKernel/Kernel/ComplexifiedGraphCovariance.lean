-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ComplexLinearMapIdentification
public import HeatKernel.Kernel.ResolventGraphCovariance

/-! # Complex extension of real operator graph covariance

A real-imaginary decomposition and compatible complex extensions transport
scaled covariance of a real resolvent graph to its complex extension.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Compatible complex extensions inherit the affine identity of a scaled real resolvent graph. -/
theorem complexified_resolvent_affine_intertwining
    (j : H →L[ℝ] E) (hspan : ∀ z : E, ∃ a b : H, z = j a + Complex.I • j b)
    (R U : H →L[ℝ] H) (Q W : E →L[ℂ] E)
    (hQ : ∀ v, Q (j v) = j (R v)) (hW : ∀ v, W (j v) = j (U v)) (c : ℝ)
    (hgraph : ∀ u g, InverseResolventGraph R u g →
      InverseResolventGraph R (U u) (c • U g)) :
    (Q.comp W).comp (c • ContinuousLinearMap.id ℂ E + (1 - c) • Q) = W.comp Q := by
  apply complexLinearMap_eq_of_real_decomposition j hspan
  intro v
  change Q (W (c • j v + (1 - c) • Q (j v))) = W (Q (j v))
  rw [hQ, ← map_smul j, ← map_smul j, ← map_add j, hW, hQ, hW]
  have h := congrArg (fun T : H →L[ℝ] H => T v)
    (resolvent_affine_intertwining_of_scaled_graph_map R U c hgraph)
  change R (U (c • v + (1 - c) • R v)) = U (R v) at h
  exact congrArg j h

/-- Compatible complex extensions inherit scaled covariance of the real resolvent graph. -/
theorem complexified_resolvent_scaled_graph_map
    (j : H →L[ℝ] E) (hspan : ∀ z : E, ∃ a b : H, z = j a + Complex.I • j b)
    (R U : H →L[ℝ] H) (Q W : E →L[ℂ] E)
    (hQ : ∀ v, Q (j v) = j (R v)) (hW : ∀ v, W (j v) = j (U v)) (c : ℝ)
    (hgraph : ∀ u g, InverseResolventGraph R u g →
      InverseResolventGraph R (U u) (c • U g))
    (u g : E) (hu : Q (u + g) = u) : Q (W u + c • W g) = W u := by
  have h := congrArg (fun T : E →L[ℂ] E => T (u + g))
    (complexified_resolvent_affine_intertwining j hspan R U Q W hQ hW c hgraph)
  change Q (W (c • (u + g) + (1 - c) • Q (u + g))) = W (Q (u + g)) at h
  rw [hu] at h
  have heq : c • (u + g) + (1 - c) • u = u + c • g := by
    rw [smul_add, sub_smul, one_smul]
    abel
  rw [heq, map_add, W.map_smul_of_tower c g] at h
  exact h

end HeatKernel
