-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalHeatOperators

/-! # Generator graph and initial limit of full-volume heat flow -/

@[expose] public section

open MeasureTheory Filter RothschildStein
open scoped Topology

namespace HeatKernel

/-- The derivative of a full-volume heat orbit is its transported negative horizontal generator. -/
theorem hasDerivAt_globalHorizontalHeatOperator {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => globalHorizontalHeatOperator G hq s.toNNReal f)
      (-globalSpatialL2Equiv n (horizontalHeatGeneratorOperator ⊤ (G.horizontalFields hq) t
        ((globalSpatialL2Equiv n).symm f))) t := by
  have h := (globalSpatialL2Equiv n).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_horizontalHeatOperator (G.horizontalFields hq) (G.horizontalFields_contDiff hq)
      ((globalSpatialL2Equiv n).symm f) ht)
  convert! h using 1
  simp only [map_neg, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- Every positive-time full-volume heat orbit lies in the concrete horizontal resolvent graph. -/
theorem inverseResolventGraph_globalHorizontalHeatOperator {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) {t : ℝ} (ht : 0 < t) :
    InverseResolventGraph (globalHorizontalFormResolvent G hq)
      (globalHorizontalHeatOperator G hq t.toNNReal f)
      (-deriv (fun s : ℝ => globalHorizontalHeatOperator G hq s.toNNReal f) t) := by
  apply (inverseResolventGraph_globalHorizontalForm_iff G hq _ _).mpr
  rw [(hasDerivAt_globalHorizontalHeatOperator G hq f ht).deriv, neg_neg,
    globalHorizontalHeatOperator_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  exact horizontalHeatOperator_mem_operatorGraph ⊤ (G.horizontalFields hq) t ht _

/-- The full-volume horizontal heat operators converge strongly to the identity at initial time. -/
theorem tendsto_globalHorizontalHeatOperator_zero {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Tendsto (fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f)
      (𝓝[>] 0) (𝓝 f) := by
  have h := ((continuous_globalHorizontalHeatOperator_apply G hq f).comp
    continuous_real_toNNReal).tendsto 0
  have hlim : Tendsto (fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f)
      (𝓝 0) (𝓝 f) := by
    simpa only [Function.comp_def, Real.toNNReal_zero, globalHorizontalHeatOperator_zero,
      ContinuousLinearMap.id_apply] using h
  exact hlim.mono_left nhdsWithin_le_nhds

end HeatKernel
