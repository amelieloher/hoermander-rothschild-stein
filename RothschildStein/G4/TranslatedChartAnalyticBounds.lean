-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxTranslation
public import RothschildStein.G4.ControlledChartPathLifting

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A coordinate translation preserves the actual derivative
and all pointwise chart estimates, on its smaller weighted domain. -/
theorem translated_chart_smooth_derivative {n : ℕ} (w : Fin n → ℕ+)
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox w (a * r)))
    {u₀ : Fin n → ℝ} (hu₀ : u₀ ∈ weightedBox w (a / 4 * r)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun u => F (u + u₀))
      (weightedBox w (a / 2 * r)) ∧
    ∀ u, fderiv ℝ (fun v => F (v + u₀)) u = fderiv ℝ F (u + u₀) := by
  refine ⟨?_, fun u => fderiv_comp_add_right u₀⟩
  exact hF.comp (contDiff_id.add contDiff_const).contDiffOn
    (fun u hu => weightedBox_half_add_quarter_mem w ha hr hu hu₀)

end RothschildStein.G4
