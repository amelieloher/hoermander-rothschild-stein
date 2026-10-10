-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.GlobalHorizontalResolvent
public import HeatKernel.Semigroup.HorizontalTimeDerivative

/-! # Horizontal heat flow on full-volume real L²

The canonical global spatial isometry transfers the concrete horizontal
heat operators and their positive-time regularity to full-volume L².
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein
open scoped NNReal

namespace HeatKernel

/-- The horizontal heat operator on full-volume real L². -/
def globalHorizontalHeatOperator {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (t : ℝ≥0) : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  (globalSpatialL2Equiv n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((horizontalHeatOperator ⊤ (G.horizontalFields hq) t).comp
      (globalSpatialL2Equiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The global spatial isometry intertwines the native and full-volume heat operators. -/
theorem globalHorizontalHeatOperator_apply {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t f = globalSpatialL2Equiv n
      (horizontalHeatOperator ⊤ (G.horizontalFields hq) t ((globalSpatialL2Equiv n).symm f)) := rfl

/-- The scalar representative is unchanged by the final global spatial transport. -/
theorem ae_globalHorizontalHeatOperator_apply {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (t : ℝ≥0) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    globalHorizontalHeatOperator G hq t f =ᵐ[volume]
      horizontalHeatOperator ⊤ (G.horizontalFields hq) t ((globalSpatialL2Equiv n).symm f) :=
  ae_globalSpatialL2Equiv _

/-- The full-volume heat operator at zero is the identity. -/
theorem globalHorizontalHeatOperator_zero {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n) :
    globalHorizontalHeatOperator G hq 0 = ContinuousLinearMap.id ℝ _ := by
  ext1 f
  rw [globalHorizontalHeatOperator_apply, horizontalHeatOperator_zero, one_apply_eq_self,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The full-volume horizontal heat operators form a semigroup. -/
theorem globalHorizontalHeatOperator_add {n q : ℕ} (G : HomogeneousGroup n) (hq : q ≤ n)
    (s t : ℝ≥0) : globalHorizontalHeatOperator G hq (s + t) =
      (globalHorizontalHeatOperator G hq s).comp (globalHorizontalHeatOperator G hq t) := by
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, globalHorizontalHeatOperator_apply,
    horizontalHeatOperator_add, mul_apply_eq_comp, LinearIsometryEquiv.symm_apply_apply]

/-- The global spatial transport preserves self-adjointness of the heat operators. -/
theorem globalHorizontalHeatOperator_isSelfAdjoint {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0) :
    IsSelfAdjoint (globalHorizontalHeatOperator G hq t) := by
  change IsSelfAdjoint ((globalSpatialL2Equiv n).conjStarAlgEquiv
    (horizontalHeatOperator ⊤ (G.horizontalFields hq) t))
  exact (horizontalHeatOperator_isSelfAdjoint ⊤ (G.horizontalFields hq) t).map
    ((globalSpatialL2Equiv n).conjStarAlgEquiv)

/-- Full-volume horizontal heat orbits are continuous at all nonnegative times. -/
theorem continuous_globalHorizontalHeatOperator_apply {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Continuous (fun t : ℝ≥0 => globalHorizontalHeatOperator G hq t f) :=
  (globalSpatialL2Equiv n).continuous.comp
    (continuous_horizontalHeatOperator_univ_apply (G.horizontalFields hq)
      (G.horizontalFields_contDiff hq) ((globalSpatialL2Equiv n).symm f))

/-- Full-volume horizontal heat orbits are continuously differentiable at positive times. -/
theorem contDiffOn_globalHorizontalHeatOperator {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    ContDiffOn ℝ 1 (fun t : ℝ => globalHorizontalHeatOperator G hq t.toNNReal f) (Set.Ioi 0) :=
  (globalSpatialL2Equiv n).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (contDiffOn_horizontalHeatOperator (G.horizontalFields hq) (G.horizontalFields_contDiff hq)
      ((globalSpatialL2Equiv n).symm f))

/-- Full-volume horizontal heat operators are contractions. -/
theorem norm_globalHorizontalHeatOperator_le_one {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (t : ℝ≥0) :
    ‖globalHorizontalHeatOperator G hq t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [globalHorizontalHeatOperator_apply, (globalSpatialL2Equiv n).norm_map, one_mul]
  calc
    ‖horizontalHeatOperator ⊤ (G.horizontalFields hq) t ((globalSpatialL2Equiv n).symm f)‖ ≤
        ‖(globalSpatialL2Equiv n).symm f‖ :=
      by simpa only [one_mul] using
        (horizontalHeatOperator ⊤ (G.horizontalFields hq) t).le_of_opNorm_le
          (norm_horizontalHeatOperator_le_one ⊤ (G.horizontalFields hq) t)
          ((globalSpatialL2Equiv n).symm f)
    _ = ‖f‖ := (globalSpatialL2Equiv n).symm.norm_map f

end HeatKernel
