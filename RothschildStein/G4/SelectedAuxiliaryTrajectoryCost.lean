-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedAuxiliaryControls
public import RothschildStein.G4.StrictConstantControlCost

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- An actual selected-plus-auxiliary trajectory has constant
short-field cost less than 2ar. The two occurrences of a field are
combined before estimating the cost (BB Prop 9.52, p. 449). -/
theorem selectedAuxiliaryTrajectory_constant_cost_lt {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → Fin m) (hB : Function.Injective B)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hr : 0 < r)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (hu : u ∈ weightedBox (w ∘ B) (a * r)) (hv : v ∈ weightedBox w (b * r))
    (γ : ℝ → (Fin n → ℝ)) (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ
        (∑ j : Fin (n + m), Fin.append u v j • Z (Fin.addCases B id j) (γ t)) t) :
    constantControlDistance Ω w Z (γ 0) (γ 1) < ENNReal.ofReal (2 * a * r) := by
  apply constantControlDistance_endpoint_lt_of_strict_controls Ω w Z γ hac hmap
    (selectedAuxiliaryControls B u v) (by positivity)
    (selectedAuxiliaryControls_mem_doubleBox w B hB ha hb hba hr hu hv)
  filter_upwards [hd] with t ht
  rw [selectedAuxiliaryControls_field_eq]
  exact ht

/-- The pure auxiliary shift has constant short-field cost less
than br, which is the quantified shift budget for the inner ball
inclusion (BB Prop 9.52, (9.49), p. 449). -/
theorem selectedAuxiliaryShift_constant_cost_lt {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → Fin m)
    {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (v : Fin m → ℝ) (hv : v ∈ weightedBox w (b * r))
    (γ : ℝ → (Fin n → ℝ)) (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hmap : MapsTo γ (Icc (0 : ℝ) 1) Ω)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ
        (∑ j : Fin (n + m), Fin.append 0 v j • Z (Fin.addCases B id j) (γ t)) t) :
    constantControlDistance Ω w Z (γ 0) (γ 1) < ENNReal.ofReal (b * r) := by
  apply constantControlDistance_endpoint_lt_of_strict_controls Ω w Z γ hac hmap v
    (mul_pos hb hr) hv
  filter_upwards [hd] with t ht
  have heq := selectedAuxiliaryControls_field_eq B (0 : Fin n → ℝ) v Z (γ t)
  rw [selectedAuxiliaryControls_zero] at heq
  rw [heq]
  exact ht

end RothschildStein.G4
