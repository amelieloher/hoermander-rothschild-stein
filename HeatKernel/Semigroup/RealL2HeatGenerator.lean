-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2HeatOperators
public import HeatKernel.Semigroup.RealHeatGenerator

/-! # Generator characterization on real L²

The canonical real-subspace equivalence transports the complex resolvent characterization
of the heat generator to the original real L² space.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem realL2SubspaceEquiv_heatOperator (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1) (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    realL2SubspaceEquiv μ (realL2HeatOperator μ R hpos hnorm t f) =
      realL2SubspaceHeatOperator μ R hpos hnorm t (realL2SubspaceEquiv μ f) :=
  (realL2SubspaceEquiv μ).apply_symm_apply _

theorem tendsto_realL2HeatOperator_differenceQuotient_iff
    (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hpos : R.IsPositive) (hnorm : ‖R‖ ≤ 1)
    (hinj : Function.Injective R) (u g : Lp ℝ 2 μ) :
    Tendsto (fun t : ℝ => t⁻¹ • (realL2HeatOperator μ R hpos hnorm t.toNNReal u - u))
      (𝓝[>] 0) (𝓝 (-g)) ↔ R (u + g) = u := by
  let e := realL2SubspaceEquiv μ
  have ht :
      Tendsto (fun t : ℝ => t⁻¹ • (realL2HeatOperator μ R hpos hnorm t.toNNReal u - u))
        (𝓝[>] 0) (𝓝 (-g)) ↔
      Tendsto (fun t : ℝ => t⁻¹ •
        (realL2SubspaceHeatOperator μ R hpos hnorm t.toNNReal (e u) - e u))
        (𝓝[>] 0) (𝓝 (-(e g))) := by
    rw [e.toHomeomorph.isEmbedding.tendsto_nhds_iff]
    simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def, map_smul, map_sub, map_neg,
      realL2SubspaceEquiv_heatOperator, e]
  have hc := tendsto_realHeatOperator_differenceQuotient_iff
    (realL2Subspace μ) (isClosed_realL2Subspace μ) (complexL2Extension μ R)
    (complexL2Extension_isSelfAdjoint μ R hpos.isSelfAdjoint)
    (mapsTo_complexL2Extension_realL2Subspace μ R)
    (spectrum_subset_Icc_of_isPositive_norm_le_one _ (complexL2Extension_isPositive μ R hpos)
      (norm_complexL2Extension_le_one μ R hnorm))
    (denseRange_complexL2Extension μ R hpos.isSelfAdjoint hinj) (e u) (e g)
  have he : complexL2Extension μ R ((e u : Lp ℂ 2 μ) + (e g : Lp ℂ 2 μ)) =
      (e u : Lp ℂ 2 μ) ↔ R (u + g) = u := by
    change complexL2Extension μ R (l2OfReal μ u + l2OfReal μ g) = l2OfReal μ u ↔ _
    rw [← (l2OfReal μ).map_add, complexL2Extension_ofReal]
    constructor
    · intro h
      have hr := congrArg (l2RealPart μ) h
      simpa only [l2RealPart_ofReal] using hr
    · intro h
      rw [h]
  exact ht.trans (hc.trans he)

end HeatKernel
