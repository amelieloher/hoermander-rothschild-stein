-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.ProductAbsorptionHolder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import RothschildStein.S.IntrinsicFlowQuotient
public import RothschildStein.S.WeakIntrinsicWords
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import RothschildStein.S.CompactFlowChart
public import RothschildStein.S.SupportedHolderExtension
public import RothschildStein.S.ContinuousWeakSupport
public import RothschildStein.G1.DriftVariation
public import RothschildStein.G1.DistanceVariation
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import RothschildStein.Definitions.rsBall
public import RothschildStein.Definitions.wordDerivative
public import RothschildStein.Definitions.wordWeight

/-!
# One cutoff product: the three estimates of the common absorption

Part of the product absorption estimate (BB p. 592 (11.75), (11.80); p. 600). For one cutoff-like function `b`
of weight `d ≤ 2` at scale `a ∈ (0, 1]` (the radial cutoff derivative bounds
`|X̃_I b| ≤ C_b a^{-(d + wordWeight I)}` and `‖b‖_{C^α} ≤ C_b a^{-(d+1)}`) and a function `u` with
weak first derivatives `F_i` on the open patch `V` (`U = sup |u|`, `D ≥ ‖F_l‖_{C^α}` for the
horizontal letters, `M ≥ ‖F_0‖_{C^α}` for the drift), the zero-extended product `w = u b` satisfies,
for every flow time `0 < η ≤ η_*`,

`‖w‖_{C^α(B)} ≤ prodBound κ q R C_b α a d M D U η`,

the explicit bound of `ProductAbsorptionArith`: it combines

* the compact weak Hölder estimate for `w`: `‖w‖_{C^α} ≤ c₀ U + κ (q H + R ‖X̃_0 w‖_∞)`, `H = D c₀ + U c₁`;
* the drift interpolation inequality (BB (2.24), (11.80)): `‖X̃_0 w‖_∞ ≤ η^{α/2} [X̃_0 w]_α + 2 η^{-1} ‖w‖_∞`;
* the seminorm bound `[X̃_0 w]_α ≤ M c₁ + κ (q (D c₂ + U c₃) + R (M c₂ + U c₄))`, obtained from
  `X̃_0 w = (X̃_0 u) b + u X̃_0 b`, the zero-extension product estimate for the first summand and
  the compact weak Hölder estimate for `u X̃_0 b` (no third-order derivative of `u` is introduced),

where `κ = 2 max(√q, 2) R^{1-α}` and `B` is the supporting control ball. The geometry is the
`(HD)` package of `RothschildStein.S.DistanceGeometry`, i.e. the `(HD)` property of the control distance of the
lifted system.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal
namespace RothschildStein.P2

variable {n q : ℕ}

theorem wordWeight_single_succ (l : Fin q) : wordWeight driftWeight [l.succ] = 1 := by
  simp [wordWeight, driftWeight, Fin.succ_ne_zero]

theorem wordWeight_single_zero : wordWeight driftWeight [(0 : Fin (q + 1))] = 2 := by
  simp [wordWeight, driftWeight]

end RothschildStein.P2
