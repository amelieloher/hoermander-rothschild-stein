-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HomogeneousMetric

/-! Coordinate points equipped with the horizontal metric and coordinate measure. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel

/-- A coordinate space whose metric is the horizontal length metric. -/
def CarnotPoint {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (_hqpos : 0 < q)
    (_hspan : bracketSpansOn univ (G.horizontalFields hq)) := Fin N → ℝ

namespace CarnotPoint
variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
  (hspan : bracketSpansOn univ (G.horizontalFields hq))

instance : MetricSpace (CarnotPoint G hq hqpos hspan) :=
  homogeneousHorizontalMetricSpace G hq hqpos hspan

instance : MeasurableSpace (CarnotPoint G hq hqpos hspan) :=
  inferInstanceAs (MeasurableSpace (Fin N → ℝ))

instance : BorelSpace (CarnotPoint G hq hqpos hspan) :=
  inferInstanceAs (BorelSpace (Fin N → ℝ))

/-- The coordinate identification is a homeomorphism for the horizontal topology. -/
def coordinateHomeomorph : CarnotPoint G hq hqpos hspan ≃ₜ (Fin N → ℝ) :=
  { Equiv.refl _ with
    continuous_toFun := continuous_id
    continuous_invFun := continuous_id }

/-- Coordinate Lebesgue measure on the horizontal metric space. -/
def volume : Measure (CarnotPoint G hq hqpos hspan) :=
  (MeasureTheory.volume : Measure (Fin N → ℝ))

/-- The metric extended distance is the literal horizontal length infimum. -/
theorem edist_eq (x y : CarnotPoint G hq hqpos hspan) :
    edist x y = horizontalL2Distance (G.horizontalFields hq) x y := rfl

/-- The horizontal coordinate space is proper when the generators have weight one. -/
theorem properSpace (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    ProperSpace (CarnotPoint G hq hqpos hspan) := by
  refine ⟨fun x R => ?_⟩
  by_cases hR : 0 ≤ R
  · have he : Metric.closedBall x R =
        {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal R} := by
      ext y
      rw [Metric.mem_closedBall, ← edist_le_ofReal hR, edist_comm, edist_eq]
      rfl
    rw [he]
    exact isCompact_horizontal_closedBall G hq hqpos hspan hw x hR
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hR)]
    exact isCompact_empty

end CarnotPoint
end HeatKernel
