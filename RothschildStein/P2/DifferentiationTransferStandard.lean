-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDriftDifferentiation
public import RothschildStein.P2.LocalRegularityReducedNoDrift
public import RothschildStein.P1.LeftDifferentiationStandard
public import RothschildStein.P1.DerivativeTransferStandard

/-!
# Differentiation and transfer on standard frames, as used by local regularity

The local regularity providers take differentiation of types (left and right) and transfer to the integration variable on the
standard frames of a lifted chart as one bundle. The standard-frame theorems
`LiftedChart.leftDifferentiation_standard`, `rightDifferentiation_standard` and `derivativeTransfer_standard` prove it for
both alphabets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P2

/-- The drift local regularity bundle of differentiation and transfer on standard frames (BB Thm 11.15,
pp. 546–551; Thm 11.24, pp. 552–559). -/
theorem differentiationTransferAllChartsDrift_holds : DifferentiationTransferAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact ⟨C.leftDifferentiation_standard hF, C.rightDifferentiation_standard hF _, C.derivativeTransfer_standard hF⟩

/-- The no-drift local regularity bundle of differentiation and transfer on standard frames (BB Thm 11.15,
pp. 546–551; Thm 11.24, pp. 552–559). -/
theorem differentiationTransferAllChartsNoDrift_holds : DifferentiationTransferAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact ⟨C.leftDifferentiation_standard hF, C.rightDifferentiation_standard hF _, C.derivativeTransfer_standard hF⟩

end RothschildStein.P2
