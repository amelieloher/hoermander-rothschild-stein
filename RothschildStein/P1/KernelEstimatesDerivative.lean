-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesBounds

/-!
# Derivative bounds in terms of the lifted control distance

The `ρ`-form bounds of `KernelEstimatesBounds` are converted to the lifted control distance `d̃`
through the comparison `ρ ≍ d̃` (lifted-chart field `gauge_comparison`): on a compact `L ⊆ U`, away from the pole,
`|X̃_{i,ξ}[K(ξ, η)]| ≤ M d̃(ξ, η)^(d - w_i)`; for the horizontal fields (`w_i = 1`) this is
`M r^(ℓ-Q-1)` and for the drift (`w_0 = 2`) it is `M r^(ℓ-Q-2)` at pole distance `r`
(BB pp. 569–571, Prop 11.32).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)
variable {Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {d : ℤ}

/-- `d̃(η, ξ) > 0` for distinct points of `U`. -/
theorem dl_toReal_pos {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) :
    0 < (C.dl η ξ).toReal :=
  ENNReal.toReal_pos (fun h => hne ((C.dl_eq_zero_iff hη hξ).mp h)) (C.dl_ne_top hη hξ)

/-- Integer powers of `ρ = ‖Θ(η, ξ)‖` are bounded by the same powers of `d̃` (via the comparison `ρ ≍ d̃`). -/
theorem gauge_zpow_le_dl {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η)
    (p : ℤ) :
    kgauge C.G (C.Θ η ξ) ^ p ≤ C.gaugeConst ^ p.natAbs * (C.dl η ξ).toReal ^ p := by
  have hρ : 0 < kgauge C.G (C.Θ η ξ) :=
    kgauge_pos C.G ((C.theta_eq_zero_iff hη hξ).not.mpr hne)
  have h1 : kgauge C.G (C.Θ η ξ) ≤ C.gaugeConst * (C.dl η ξ).toReal := by
    have := C.gauge_div_le_dl_toReal hη hξ
    rwa [div_le_iff₀ C.gaugeConst_pos, mul_comm] at this
  exact kzpow_le_const_mul C.one_le_gaugeConst hρ (C.dl_toReal_pos hη hξ hne) h1
    (C.dl_toReal_le hη hξ) p

/-- Derivative bound along `X̃_i` in terms of the lifted control distance: on a compact
subset `L` of `U`, `|X̃_{i,ξ}[K(ξ, η)]| ≤ M d̃(ξ, η)^(d - w_i)` away from the pole (by the chart chain rule,
BB pp. 569–571). With `d = ℓ - Q` the horizontal fields give `r^(ℓ-Q-1)`, the drift `r^(ℓ-Q-2)`. -/
theorem exists_derivative_bound (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hWB : HasWeightedBounds C.G d Ψ) {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) (i : Fin k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ η ∈ L, ∀ z ∈ L, z ≠ η →
      |fderiv ℝ (fun ξ => Ψ ξ η (C.Θ η ξ)) z (C.Xl i z)| ≤
        M * ((C.dl z η).toReal) ^ (d - ((w i : ℕ) : ℤ)) := by
  obtain ⟨M, hM0, hM⟩ := C.exists_derivative_bound_gauge hΨ hWB hL hLU i
  have hc : 0 ≤ C.gaugeConst ^ (d - ((w i : ℕ) : ℤ)).natAbs := by
    have := C.gaugeConst_pos
    positivity
  refine ⟨M * C.gaugeConst ^ (d - ((w i : ℕ) : ℤ)).natAbs, mul_nonneg hM0 hc, ?_⟩
  intro η hη z hz hne
  rw [C.dl_symm z η]
  calc _ ≤ M * kgauge C.G (C.Θ η z) ^ (d - ((w i : ℕ) : ℤ)) := hM η hη z hz hne
    _ ≤ M * (C.gaugeConst ^ (d - ((w i : ℕ) : ℤ)).natAbs *
          (C.dl η z).toReal ^ (d - ((w i : ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left (C.gauge_zpow_le_dl (hLU hη) (hLU hz) hne _) hM0
    _ = _ := by ring

end LiftedChart
end RothschildStein.P1
