-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.ProductAbsorptionExit
public import RothschildStein.P2.ProductAbsorptionWeak
public import RothschildStein.S.CompactUniformWordApproximation
public import RothschildStein.S.MollifierUniformAllDimensions
public import RothschildStein.S.MollifierCompactAllDimensions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import RothschildStein.G1.DistanceVariation
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import RothschildStein.G1.WeightedTriangle
public import RothschildStein.Definitions.rsBall
public import RothschildStein.S.ContinuousWeakSupport
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import RothschildStein.G1.DriftVariation
public import RothschildStein.S.HolderProducts
public import RothschildStein.S.HolderArithmetic
public import RothschildStein.S.DistanceMetricLaws
public import RothschildStein.S.HolderSubsetContinuity
public import RothschildStein.Definitions.driftWeight

/-!
# Hölder seminorms of cutoff products

Part of the product absorption estimate: function-level ingredients (BB p. 592 (11.75); p. 600). For a
product `u c` with `c` supported in a compact `K` inside the open patch `V` where `u` has weak
first derivatives, the compact weak Hölder estimate (BB (2.19))
(`RothschildStein.S.compact_weak_drift_holderSeminorm_supremum_le`) bounds the Hölder seminorm
on the supporting control ball by the suprema of the weak first derivatives
`g_i = (X_i u) c + u X_i c` of the zero extension. The Hölder norm of a product `f b`
on a larger set agrees with that on `V` (first exit, `holderENorm_cutoff_product_eq`) and obeys
the product estimate (BB (2.20)–(2.21)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.P2

variable {n q : ℕ}

theorem driftWeight_le_two (i : Fin (q + 1)) : (driftWeight i : ℕ) ≤ 2 := by
  by_cases hi : i = 0 <;> simp [driftWeight, hi]

end RothschildStein.P2
