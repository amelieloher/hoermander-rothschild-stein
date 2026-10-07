-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledReparam
public import RothschildStein.G2.ControlMeasure
public import RothschildStein.G2.BallTopology
public import RothschildStein.S.DistanceGeometry
public import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {N m : ℕ}

/-- The full published
control-norm conclusion gives an actual metric whose topology is
exactly the Euclidean topology (BB Thm 3.54, pp. 125–127). -/
@[instance_reducible]
def groupControlMetric_of_controlNorm
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (H : G2.ControlNormConclusion G w X) : MetricSpace (Fin N → ℝ) := by
  let d := G2.gaugeDistance G H.norm
  have hc : ∀ x y,d x y = d y x := by
    intro x y
    change G2.gaugeDistance G H.norm x y = G2.gaugeDistance G H.norm y x
    rw [← G2.controlDistance_toReal_of_controlNorm G H x y,
      ← G2.controlDistance_toReal_of_controlNorm G H y x]
    rw [G1.controlDistance_symm univ w X x y]
  refine MetricSpace.ofDistTopology d
    (fun x => (G2.gaugeDistance_eq_zero_iff G H.norm.gauge x x).mpr rfl) hc
    (fun x y z => ?_) (fun U => ?_)
    (fun x y h => (G2.gaugeDistance_eq_zero_iff G H.norm.gauge x y).mp h)
  · simpa only [H.constant_one,one_mul] using G2.gaugeDistance_triangle G H.norm x z y
  · constructor
    · intro h x hx
      obtain ⟨r,hr,hsub⟩ := (G2.isOpen_iff_gaugeBall H.norm.gauge U).mp h x hx
      refine ⟨r,hr,fun y hy => hsub ?_⟩
      change d y x < r
      rwa [hc y x]
    · intro h
      apply (G2.isOpen_iff_gaugeBall H.norm.gauge U).mpr
      intro x hx
      obtain ⟨r,hr,hsub⟩ := h x hx
      refine ⟨r,hr,fun y hy => hsub y ?_⟩
      change d y x < r at hy
      rwa [hc y x] at hy

/-- Restriction preserves
one fixed actual ambient group control distance and Euclidean topology.
The certificate is constructed, rather than assumed as a separate
compatibility premise (BB Thm 3.54(v), pp. 125–127). -/
def groupControlGeometry_of_controlNorm
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (H : G2.ControlNormConclusion G w X) (U : Opens (Fin N → ℝ)) :
    DistanceGeometry U := by
  let M := groupControlMetric_of_controlNorm G w X H
  let MU := MetricSpace.induced (fun x : U => x.val) Subtype.val_injective M
  refine ⟨controlDistance univ w X,(@MetricSpace.toEMetricSpace U MU),?_,rfl⟩
  intro x y
  rw [@edist_dist U MU.toPseudoMetricSpace x y]
  change ENNReal.ofReal (G2.gaugeDistance G H.norm x.val y.val) =
    controlDistance univ w X x.val y.val
  exact (H.distance_eq x.val y.val).symm

end RothschildStein.S
