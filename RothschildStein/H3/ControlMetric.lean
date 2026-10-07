-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.GaugeConsequences
public import RothschildStein.G2.BallTopology
public import RothschildStein.G2.ControlMeasure
public import Mathlib.Topology.MetricSpace.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open RothschildStein.G2
/-- A carrier separating the control metric from the coordinate norm. -/
def ControlCarrier (N : ℕ) := Fin N → ℝ

instance controlCarrierZero (N : ℕ) : Zero (ControlCarrier N) :=
  inferInstanceAs (Zero (Fin N → ℝ))

instance controlCarrierTopology (N : ℕ) : TopologicalSpace (ControlCarrier N) :=
  inferInstanceAs (TopologicalSpace (Fin N → ℝ))

instance controlCarrierSecondCountable (N : ℕ) : SecondCountableTopology (ControlCarrier N) :=
  inferInstanceAs (SecondCountableTopology (Fin N → ℝ))

instance controlCarrierMeasureSpace (N : ℕ) : MeasureSpace (ControlCarrier N) :=
  inferInstanceAs (MeasureSpace (Fin N → ℝ))

instance controlCarrierBorel (N : ℕ) : BorelSpace (ControlCarrier N) :=
  inferInstanceAs (BorelSpace (Fin N → ℝ))

instance controlCarrierNullSingleton (N : ℕ) [Nonempty (Fin N)] :
    NullSingletonClass (volume : Measure (ControlCarrier N)) :=
  inferInstanceAs (NullSingletonClass (volume : Measure (Fin N → ℝ)))

variable {N : ℕ} (G : HomogeneousGroup N)

/-- Gauge balls form neighborhoods for the coordinate topology.
BB Theorem 3.20, pp. 104–105; needed to retain the Borel and volume structures. -/
theorem gaugeDistance_open_iff (ν : HomogeneousNorm G) (hsym : ν.Symmetric)
    (s : Set (Fin N → ℝ)) : IsOpen s ↔
      ∀ x ∈ s, ∃ ε > 0, ∀ y, gaugeDistance G ν x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hb⟩ := gaugeBall_basis ν.gauge hs hx
    refine ⟨ε, hε, fun y hy => hb ?_⟩
    change gaugeDistance G ν y x < ε
    rwa [gaugeDistance_symmetric G ν hsym x y]
  · intro h
    apply (isOpen_iff_gaugeBall ν.gauge s).mpr
    intro x hx
    obtain ⟨ε, hε, hb⟩ := h x hx
    refine ⟨ε, hε, fun y hy => hb y ?_⟩
    change gaugeDistance G ν y x < ε at hy
    rwa [gaugeDistance_symmetric G ν hsym x y] at hy

/-- The control-gauge metric has definitionally the original coordinate
 topology; no change of the volume measure or measurable space is made. -/
@[instance_reducible]
def gaugeMetric (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric) :
    MetricSpace (ControlCarrier N) :=
  MetricSpace.ofDistTopology (α := ControlCarrier N) (gaugeDistance G ν)
    (fun x => (gaugeDistance_eq_zero_iff G ν.gauge x x).mpr rfl)
    (fun x y => (gaugeDistance_symmetric G ν hsym x y).symm)
    (fun x y z => by
      simpa only [h1, one_mul] using gaugeDistance_triangle G ν x z y)
    (gaugeDistance_open_iff G ν hsym)
    (fun x y h => (gaugeDistance_eq_zero_iff G ν.gauge x y).mp h)

/-- Under the global control-norm comparison, the carrier metric is the
real-valued control distance. -/
theorem gaugeMetric_controlDistance {m : ℕ} {w : Fin m → ℕ+}
    {Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G w Y) (x y : ControlCarrier N) :
    @dist (ControlCarrier N) (gaugeMetric G H.norm H.constant_one H.symmetric).toDist x y =
      (controlDistance Set.univ w Y x y).toReal := by
  change gaugeDistance G H.norm x y = _
  exact (controlDistance_toReal_of_controlNorm G H x y).symm

end RothschildStein.H3
