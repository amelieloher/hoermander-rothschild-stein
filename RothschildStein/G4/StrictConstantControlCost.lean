-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- Strict constant coefficient bounds give a strict distance
bound for an actual AC trajectory, using one common smaller positive
cost for all coordinates (BB Prop 9.52, p. 449). -/
theorem constantControlDistance_endpoint_lt_of_strict_controls {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (γ : ℝ → (Fin n → ℝ)) (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) Ω) (c : Fin m → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hc : c ∈ weightedBox w ρ)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ (∑ J, c J • Z J (γ t)) t) :
    constantControlDistance Ω w Z (γ 0) (γ 1) < ENNReal.ofReal ρ := by
  obtain ⟨δ, hδ, hδρ, hbound⟩ := exists_smaller_weighted_cost w hρ hc
  have hcurve : IsConstantControlledCurve Ω w Z δ γ :=
    ⟨hδ, hac, hmap, c, hbound, hd⟩
  have hcost : constantControlDistance Ω w Z (γ 0) (γ 1) ≤ ENNReal.ofReal δ :=
    sInf_le ⟨δ, rfl, γ, hcurve, rfl, rfl⟩
  exact hcost.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr hδρ)

end RothschildStein.G4
