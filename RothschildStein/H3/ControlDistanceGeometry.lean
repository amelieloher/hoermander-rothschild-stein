-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.S.DistanceGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The global control-norm and metric-comparison hypotheses give the
shared S geometry on the whole group with its original Euclidean topology. -/
def controlDistanceGeometry_of_controlNorm {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (C : G2.ControlNormConclusion G w X) :
    S.DistanceGeometry (⊤ : Opens (Fin N → ℝ)) := by
  letI metric : MetricSpace (Fin N → ℝ) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let submetric : MetricSpace (⊤ : Opens (Fin N → ℝ)) :=
    @Subtype.metricSpace (Fin N → ℝ) (fun _ => True) metric
  refine ⟨controlDistance univ w X, submetric.toEMetricSpace, ?_, rfl⟩
  intro x y
  rw [@edist_dist (⊤ : Opens (Fin N → ℝ)) submetric.toPseudoMetricSpace x y]
  change ENNReal.ofReal (G2.gaugeDistance G C.norm x.val y.val) =
    controlDistance univ w X x.val y.val
  exact (C.distance_eq x.val y.val).symm

end RothschildStein.H3
