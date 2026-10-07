-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialFlowMaps
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

theorem curve_timeOne_eq_initial_of_zero_velocity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ → E} (hα : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt α 0 t) : α 1 = α 0 := by
  have hb : ‖α 1 - α 0‖ ≤ (0 : ℝ) :=
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hα t ht).hasDerivWithinAt) (fun _ _ => by simp)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

theorem finiteLieTimeOneMap_zero_of_finiteLie_ode
    {a s N : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (hinit : Φ ((0, x), 0) = x)
    (hODE : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun v => Φ ((0, x), v))
      (finiteLieField D X 0 (Φ ((0, x), t))) t) :
    finiteLieTimeOneMap Φ (0, x) = x := by
  have he := curve_timeOne_eq_initial_of_zero_velocity (α := fun t => Φ ((0, x), t)) (by
    intro t ht
    have ht' : t ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [ht.1, ht.2]
    simpa only [finiteLieField, map_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
      using hODE t ht')
  exact he.trans hinit

end RothschildStein.G3
