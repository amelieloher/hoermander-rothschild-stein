-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped ENNReal

/-- Every weighted point value is bounded by a finite real Phi value. -/
theorem phi_point_le_toReal (I : Set ℝ) (N : ℝ → ℝ) (r : ℝ) (k : ℕ)
    (σ : ℝ) (hσ : σ ∈ I) (hfin : phi I r k N ≠ ⊤) :
    (1-σ)^k * r^k * N σ ≤ (phi I r k N).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  exact le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)

end RothschildStein.H3
