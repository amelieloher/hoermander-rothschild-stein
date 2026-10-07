-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.OriginalLocalDoubling
public import RothschildStein.P2.LocalRegularityHypotheses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G4

/-- The exact RS-3 drift doubling input on every projected
lifted-chart neighborhood, constructed from smoothness and original rank
(BB Theorem 9.1, p. 400). -/
theorem localDoublingAllChartsDrift : P2.LocalDoublingAllChartsDrift := by
  intro n q s m hn _hq Ω hΩ X x₀ hX hrank C
  apply originalLocalDoubling_of_smooth_bracketSpans (by omega) hΩ ?_ driftWeight X hX hrank
  rintro y ⟨ξ,hξ,rfl⟩
  exact C.closure_U_subset (subset_closure hξ)

/-- The exact RS-3 no-drift doubling input on every projected
lifted-chart neighborhood, including the vacuous zero-generator case
(BB Theorem 9.1, p. 400). -/
theorem localDoublingAllChartsNoDrift : P2.LocalDoublingAllChartsNoDrift := by
  intro n q s m hn Ω hΩ X x₀ hX hrank C
  apply originalLocalDoubling_of_smooth_bracketSpans (by omega) hΩ ?_ noDriftWeight X hX hrank
  rintro y ⟨ξ,hξ,rfl⟩
  exact C.closure_U_subset (subset_closure hξ)
end RothschildStein.G4
