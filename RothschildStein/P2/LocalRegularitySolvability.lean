-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityHypotheses
public import RothschildStein.P2.SolvabilityFull
public import RothschildStein.P2.SolvabilityFullNoDrift
public import RothschildStein.H1.CompleteAssembly

/-!
# Local regularity assembly: the local solvability theorem from `LeftDifferentiation`

The roots take left differentiation (`LeftDifferentiationAllChartsDrift`, `LeftDifferentiationAllChartsNoDrift`: `LeftDifferentiation` for every standard frame of
every lifted chart) as their hypothesis, not the local solvability theorem. Local solvability is recovered here: the H1
fundamental kernel `K` of the model of a chart exists unconditionally (`H1.exists_globalFundamentalKernel`,
the dimension hypothesis `Q > 2` from `3 ≤ n`), has all the fundamental-kernel properties (`H1.assemble_kernel`), the smooth
homogeneous norm of the chart group is symmetric and smooth, and
`localSolvability_of_leftDifferentiation` / `localSolvabilityNoDrift_of_leftDifferentiation` (`SolvabilityFull*`) give the exact
statement `LocalSolvability C` / `LocalSolvabilityNoDrift C` for every chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open RothschildStein.P1
namespace RothschildStein.P2

/-- Local solvability for smoothing with drift in every lifted drift chart over a system
with `3 ≤ n` and `0 < q`, from the hypothesis `LeftDifferentiation` (left differentiation of types) for the standard
frames of the charts. -/
theorem localSolvabilityAllChartsDrift_of_leftDifferentiation (h : LeftDifferentiationAllChartsDrift) : LocalSolvabilityAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.driftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  refine localSolvability_of_leftDifferentiation K hQ (fun u => ?_) (G2.smoothNorm_smooth C.G)
    (H1.assemble_kernel K hQ) (h hn hq C K)
  have hu := C.smoothNorm_symmetric u
  rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu

/-- Local solvability for smoothing without drift in every lifted no-drift chart over a
system with `3 ≤ n` and `0 < q`, from the hypothesis `LeftDifferentiation` (left differentiation of types) for the
standard frames of the charts. -/
theorem localSolvabilityAllChartsNoDrift_of_leftDifferentiation (h : LeftDifferentiationAllChartsNoDrift) : LocalSolvabilityAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.noDriftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  refine localSolvabilityNoDrift_of_leftDifferentiation K hQ (fun u => ?_) (G2.smoothNorm_smooth C.G)
    (H1.assemble_kernel K hQ) (h hn hq C K)
  have hu := C.smoothNorm_symmetric u
  rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu

end RothschildStein.P2
