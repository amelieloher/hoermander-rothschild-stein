-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Order.Compact
public import RothschildStein.Definitions.controlDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal Topology
namespace RothschildStein.S

/-- Distance assumptions on a fixed ambient open domain:
the chosen extended metric induces the Euclidean subtype topology
(BB Def 1.38, p. 21; Thm 1.53, p. 35). This structure does not change
the ambient metric or choose a new distance after restriction. -/
structure DistanceGeometry {n : ℕ} (Ω : Opens (Fin n → ℝ)) where
  d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞
  metric : EMetricSpace Ω
  distance_eq : ∀ x y : Ω, @edist Ω metric.toEDist x y = d x.val y.val
  topology_eq : (inferInstance : TopologicalSpace Ω) = metric.toUniformSpace.toTopologicalSpace

/-- A local Euclidean-to-control distance bound on a specified patch (BB Theorem 1.53, (1.45), p. 35). -/
def DistanceComparison {n : ℕ} (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ x ∈ V, ∀ y ∈ V, ENNReal.ofReal ‖x-y‖ ≤ ENNReal.ofReal κ*d x y

/-- The compatible metric on the open subtype retains the Euclidean subtype topology. -/
@[instance_reducible]
def DistanceGeometry.compatibleMetric {n : ℕ} {Ω : Opens (Fin n → ℝ)}
    (G : DistanceGeometry Ω) : EMetricSpace Ω := G.metric.replaceTopology G.topology_eq

/-- Each distance section is Euclidean-continuous, even when
its values may be infinite (BB Prop 1.41 and Thm 1.53). -/
theorem DistanceGeometry.continuous_distance {n : ℕ} {Ω : Opens (Fin n → ℝ)}
    (G : DistanceGeometry Ω) (x : Ω) : Continuous (fun y : Ω => G.d x.val y.val) := by
  have H := @continuous_edist Ω G.compatibleMetric.toPseudoEMetricSpace
  have ht := H.comp ((continuous_const : Continuous (fun _ : Ω => x)).prodMk continuous_id)
  simpa only [Function.comp_def,id_eq,G.distance_eq] using ht

/-- Ambient distance balls are open for the Euclidean
subtype topology (BB Thm 1.53, p. 35). -/
theorem DistanceGeometry.isOpen_ball_subtype {n : ℕ} {Ω : Opens (Fin n → ℝ)}
    (G : DistanceGeometry Ω) (x : Ω) (R : ℝ≥0∞) :
    IsOpen {y : Ω | G.d x.val y.val < R} :=
  isOpen_lt (G.continuous_distance x) continuous_const

end RothschildStein.S
