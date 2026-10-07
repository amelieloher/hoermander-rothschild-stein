-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalDisplacement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators ENNReal

namespace RothschildStein.G1

/-- A local first-exit buffer bounds the extended distance from
below, without any global coefficient bound or connectivity assumption
(BB Props 1.37/1.42, pp. 20–24). -/
theorem controlDistance_lower_bound_of_buffer {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) (x y : Fin n → ℝ) {B R : ℝ}
    (hB : 0 < B) (hR : 0 < R)
    (hbound : ∀ z, ‖z - x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) :
    ENNReal.ofReal (min 1 (min (R / B) (‖y - x‖ / B))) ≤ controlDistance Ω w X x y := by
  apply le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hγ0, hγ1⟩
  apply ENNReal.ofReal_le_ofReal
  by_cases hδ : 1 ≤ δ
  · exact (min_le_left _ _).trans hδ
  by_cases hlarge : R ≤ δ * B
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans ((div_le_iff₀ hB).mpr hlarge)
  have hm := controlledCurve_endpoint_displacement_le hw hγ (le_of_not_ge hδ)
    hB.le hR (lt_of_not_ge hlarge) (by simpa only [hγ0] using hbound)
  rw [hγ0, hγ1] at hm
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans ((div_le_iff₀ hB).mpr hm)

/-- The near-diagonal lower bound is Euclidean-linear, with
explicit radius depending only on the local buffer and field bound
(BB Props 1.37/1.42, pp. 20–24). -/
theorem controlDistance_linear_lower_bound {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hw : ∀ i, (w i : ℕ) ≤ 2) (x y : Fin n → ℝ) {B R : ℝ}
    (hB : 0 < B) (hR : 0 < R)
    (hbound : ∀ z, ‖z - x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B)
    (hnear : ‖y - x‖ ≤ min B R) :
    ENNReal.ofReal (‖y - x‖ / B) ≤ controlDistance Ω w X x y := by
  have h1 : ‖y - x‖ / B ≤ 1 := (div_le_one hB).mpr (hnear.trans (min_le_left _ _))
  have h2 : ‖y - x‖ / B ≤ R / B :=
    div_le_div_of_nonneg_right (hnear.trans (min_le_right _ _)) hB.le
  simpa only [min_eq_right h2, min_eq_right h1] using
    controlDistance_lower_bound_of_buffer hw x y hB hR hbound

end RothschildStein.G1
