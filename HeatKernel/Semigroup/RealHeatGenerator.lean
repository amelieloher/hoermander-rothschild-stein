-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealHeatOperators
public import HeatKernel.Semigroup.PositiveResolventSpectrum

/-! # Generator identification on an invariant real subspace

The right difference quotient of the restricted real semigroup has the same resolvent
characterization as the ambient complex semigroup.
-/

@[expose] public section
open Set Filter
open scoped Topology NNReal
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tendsto_realHeatOperator_differenceQuotient_iff
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (hinv : MapsTo R S S)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (hdense : DenseRange R) (u g : S) :
    Tendsto (fun t : ℝ => t⁻¹ •
      (realHeatOperator S hS R hR hinv hspec t.toNNReal u - u))
      (𝓝[>] 0) (𝓝 (-g)) ↔ R ((u : E) + (g : E)) = (u : E) := by
  rw [tendsto_subtype_rng]
  have heq : (fun t : ℝ => ((t⁻¹ •
      (realHeatOperator S hS R hR hinv hspec t.toNNReal u - u) : S) : E))
      =ᶠ[𝓝[>] 0] (fun t : ℝ => t⁻¹ •
        ((cfc (heatMultiplier t) R : E →L[ℂ] E) (u : E) - (u : E))) := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    simp only [Submodule.coe_smul, Submodule.coe_sub, coe_realHeatOperator_apply]
    unfold heatOperator
    have hf : semigroupMultiplier t.toNNReal = heatMultiplier t := by
      ext r
      rw [semigroupMultiplier_of_pos (Real.toNNReal_pos.mpr ht'), Real.coe_toNNReal t ht'.le]
    rw [hf]
  rw [Filter.tendsto_congr' heq]
  exact tendsto_heat_cfc_differenceQuotient_iff R hR hspec hdense u g

end HeatKernel
