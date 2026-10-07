-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierDefs
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Set Metric
open scoped Topology
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A normalized smooth group bump exists for every homogeneous norm
(BB Prop 3.48, p. 121; Euclidean bump construction in the gauge unit ball). -/
theorem nonempty_groupMollifier (ν : HomogeneousNorm G) : Nonempty (GroupMollifier G ν) := by
  have hzero : ν (0 : Fin N → ℝ) = 0 := (ν.gauge.2.2.1 0).mpr rfl
  have hopen : IsOpen {x | ν x < 1} := isOpen_lt ν.gauge.1 continuous_const
  have hzmem : (0 : Fin N → ℝ) ∈ {x | ν x < 1} := by
    change ν 0 < 1
    rw [hzero]
    exact zero_lt_one
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzmem)
  let b : ContDiffBump (0 : Fin N → ℝ) :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  refine ⟨⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed,
    b.nonneg_normed, b.integral_normed, ?_⟩⟩
  intro x hx
  by_contra hn
  have hs : x ∈ Function.support (b.normed volume) := hn
  rw [b.support_normed_eq] at hs
  exact (not_lt_of_ge hx) (hball hs)

end RothschildStein.G2
