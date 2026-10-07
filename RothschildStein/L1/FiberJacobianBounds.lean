-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberChartJacobian

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.L1

/-- Two-sided full and horizontal Jacobian bounds give the
full two-sided vertical ratio bound (BB pp. 520–522, repaired lower ratio). -/
theorem abs_vertical_jacobian_bounds_of_ratio
    {v A H a b c d : ℝ} (hidentity : |v| = |A| / |H|)
    (ha : 0 ≤ a) (hc : 0 < c)
    (hAlo : a ≤ |A|) (hAhi : |A| ≤ b) (hHlo : c ≤ |H|) (hHhi : |H| ≤ d) :
    a / d ≤ |v| ∧ |v| ≤ b / c := by
  have hH : 0 < |H| := hc.trans_le hHlo
  have hb : 0 ≤ b := (abs_nonneg A).trans hAhi
  rw [hidentity]
  constructor
  · exact (div_le_div_of_nonneg_left ha hH hHhi).trans
      (div_le_div_of_nonneg_right hAlo hH.le)
  · exact (div_le_div_of_nonneg_right hAhi hH.le).trans
      (div_le_div_of_nonneg_left hb hc hHlo)

end RothschildStein.L1
