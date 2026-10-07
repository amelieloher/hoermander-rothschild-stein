-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartDataRestriction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G4

/-- Increasing the chart constants preserves all actual analytic
estimates. This allows finite spatial covers to share one pair of constants. -/
theorem chartAnalyticBounds_enlarge_constants {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {B : Fin n → Fin m}
    {F : (Fin n → ℝ) → (Fin n → ℝ)} {Q : Set (Fin n → ℝ)}
    {r κ D κ' D' : ℝ} (hr : 0 ≤ r)
    (h : ChartAnalyticBounds Ω w Z B F Q r κ D)
    (hκ : κ ≤ κ') (hD : D ≤ D') :
    ChartAnalyticBounds Ω w Z B F Q r κ' D' := by
  obtain ⟨hF, hmap, hjac, hdet, herr, hframe⟩ := h
  refine ⟨hF, hmap, hjac, hdet, ?_, ?_⟩
  · intro u hu j i
    exact (herr u hu j i).trans
      (mul_le_mul_of_nonneg_right hκ (zpow_nonneg hr _))
  · intro u hu J j
    exact (hframe u hu J j).trans
      (mul_le_mul_of_nonneg_right hD (zpow_nonneg hr _))

end RothschildStein.G4
