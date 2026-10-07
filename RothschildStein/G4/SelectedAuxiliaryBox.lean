-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedAuxiliaryFamily
public import RothschildStein.G4.WeightedCoefficientBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The two strict weighted boxes lie in the coefficient domain
of the actual selected-plus-auxiliary flow (BB Prop 9.52, p. 448). -/
theorem selectedAuxiliary_coefficients_le {k n s : ℕ}
    (w : Fin k → ℕ+) (B : Fin n → ShortWord w s)
    {a b e r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hae : a ≤ e) (hbe : b ≤ e)
    (u : Fin n → ℝ) (v : Fin (Fintype.card (ShortWord w s)) → ℝ)
    (hu : u ∈ weightedBox (shortWeight w ∘ B) (a * r))
    (hv : v ∈ weightedBox (fun j => shortWeight w (shortIndex w j)) (b * r)) :
    ∀ j, |Fin.append u v j| ≤
      (e * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ) := by
  refine Fin.addCases ?_ ?_
  · intro i
    simpa only [Fin.append_left, selectedAuxiliaryIndex_selected] using
      (hu i).le.trans (pow_le_pow_left₀ (mul_nonneg ha hr)
        (mul_le_mul_of_nonneg_right hae hr) (shortWeight w (B i) : ℕ))
  · intro j
    simpa only [Fin.append_right, selectedAuxiliaryIndex_auxiliary] using
      (hv j).le.trans (pow_le_pow_left₀ (mul_nonneg hb hr)
        (mul_le_mul_of_nonneg_right hbe hr) (shortWeight w (shortIndex w j) : ℕ))

end RothschildStein.G4
