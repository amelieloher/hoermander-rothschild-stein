-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.P1.KernelEstimatesHomogeneous
public import RothschildStein.G1.WeightedTriangle
public import RothschildStein.G1.ControlledReparam
public import RothschildStein.G1.ControlledBasics

/-!
# Chart facts for kernel estimates

Elementary consequences of the `LiftedChart` fields: the comparison constant `Cρ` between the max
gauge of `Θ(η, ξ)` and the lifted control distance `d̃(η, ξ)`, finiteness and the triangle
inequality for `d̃` on the coordinate neighborhood `U`, injectivity of `ξ ↦ Θ(η, ξ)`, and
smoothness/compactness bounds (BB pp. 483–485, 509–517, 569–571).
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

/-- The lifted coordinate neighborhood lies in the lifted domain. -/
theorem U_subset_O : C.U ⊆ C.O := fun _ hz => C.closure_U_subset (subset_closure hz)

/-- The comparison constant `Cρ` between `ρ = ‖Θ(η, ξ)‖` and `d̃` (lifted-chart field `gauge_comparison`). -/
def gaugeConst : ℝ := Classical.choose C.gauge_comparison

/-- `1 ≤ Cρ`. -/
theorem one_le_gaugeConst : 1 ≤ C.gaugeConst := (Classical.choose_spec C.gauge_comparison).1

/-- `0 < Cρ`. -/
theorem gaugeConst_pos : 0 < C.gaugeConst := zero_lt_one.trans_le C.one_le_gaugeConst

/-- The two-sided comparison `‖Θ(η, ξ)‖ / Cρ ≤ d̃(η, ξ) ≤ Cρ ‖Θ(η, ξ)‖` on `U × U` (lifted-chart field `gauge_comparison`). -/
theorem gaugeConst_spec : ∀ η ∈ C.U, ∀ ξ ∈ C.U,
    ENNReal.ofReal (kgauge C.G (C.Θ η ξ) / C.gaugeConst) ≤ C.dl η ξ ∧
      C.dl η ξ ≤ ENNReal.ofReal (C.gaugeConst * kgauge C.G (C.Θ η ξ)) :=
  (Classical.choose_spec C.gauge_comparison).2

/-- The lifted control distance is finite on `U × U`. -/
theorem dl_ne_top {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) : C.dl η ξ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (C.gaugeConst_spec η hη ξ hξ).2

/-- `d̃ ≤ Cρ ‖Θ‖`. -/
theorem dl_toReal_le {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    (C.dl η ξ).toReal ≤ C.gaugeConst * kgauge C.G (C.Θ η ξ) :=
  ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg C.gaugeConst_pos.le (kgauge_nonneg C.G _)) (C.gaugeConst_spec η hη ξ hξ).2

/-- `‖Θ‖ / Cρ ≤ d̃`. -/
theorem gauge_div_le_dl_toReal {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    kgauge C.G (C.Θ η ξ) / C.gaugeConst ≤ (C.dl η ξ).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (C.dl_ne_top hη hξ)).mp (C.gaugeConst_spec η hη ξ hξ).1

/-- `ξ ↦ Θ(η, ξ)` is smooth on `U`. -/
theorem theta_contDiffOn_right {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Θ η) C.U := by
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ : Fin (n + m) → ℝ => (η, ξ)) C.U :=
    contDiffOn_const.prodMk contDiffOn_id
  exact C.theta_smooth.comp hf (fun ξ hξ => ⟨hη, hξ⟩)

/-- `(η, ξ) ↦ Θ(η, ξ)` is continuous on `U × U`. -/
theorem theta_continuousOn : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    C.Θ z.1 z.2) (C.U ×ˢ C.U) := C.theta_smooth.continuousOn

/-- `Θ(η, ξ) = 0` exactly when `ξ = η`, for `η, ξ ∈ U`. -/
theorem theta_eq_zero_iff {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    C.Θ η ξ = 0 ↔ ξ = η := by
  obtain ⟨hsrc, heq, -, -, h0⟩ := C.chart η hη
  constructor
  · intro h
    have h1 : C.e η ξ = C.e η η := by rw [heq ξ hξ, heq η hη, h, h0]
    exact (C.e η).injOn (by rw [hsrc]; exact hξ) (by rw [hsrc]; exact hη) h1
  · rintro rfl
    exact h0

/-- `(η, Θ(η, ξ)) ∈ T` for `η, ξ ∈ U`. -/
theorem mem_T_theta {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    (η, C.Θ η ξ) ∈ C.T := by
  obtain ⟨hsrc, heq, -, -, -⟩ := C.chart η hη
  refine ⟨hη, ?_⟩
  rw [← heq ξ hξ]
  exact (C.e η).map_source (by rw [hsrc]; exact hξ)

/-- `(η, 0) ∈ T` for `η ∈ U`. -/
theorem mem_T_zero {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : (η, (0 : Fin (n + m) → ℝ)) ∈ C.T := by
  obtain ⟨-, -, -, -, h0⟩ := C.chart η hη
  have := C.mem_T_theta hη hη
  rwa [h0] at this

/-- `d̃(η, ξ) = 0` exactly when `ξ = η`, for `η, ξ ∈ U`. -/
theorem dl_eq_zero_iff {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    C.dl η ξ = 0 ↔ ξ = η := by
  constructor
  · intro h
    have h1 := C.gauge_div_le_dl_toReal hη hξ
    rw [h, ENNReal.toReal_zero] at h1
    have h2 : kgauge C.G (C.Θ η ξ) ≤ 0 := by
      have := mul_le_mul_of_nonneg_right h1 C.gaugeConst_pos.le
      rwa [zero_mul, div_mul_cancel₀ _ C.gaugeConst_pos.ne'] at this
    exact (C.theta_eq_zero_iff hη hξ).mp
      ((kgauge_eq_zero_iff C.G _).mp (le_antisymm h2 (kgauge_nonneg C.G _)))
  · rintro rfl
    exact RothschildStein.G1.controlDistance_self w C.Xl (C.U_subset_O hη)

/-- Symmetry of `d̃`. -/
theorem dl_symm (a b : Fin (n + m) → ℝ) : C.dl a b = C.dl b a :=
  RothschildStein.G1.controlDistance_symm C.O w C.Xl a b

/-- Triangle inequality for `d̃` (real values on `U`). -/
theorem dl_toReal_triangle {a b c : Fin (n + m) → ℝ} (ha : a ∈ C.U) (hb : b ∈ C.U)
    (hc : c ∈ C.U) : (C.dl a c).toReal ≤ (C.dl a b).toReal + (C.dl b c).toReal := by
  have h := RothschildStein.G1.controlDistance_triangle C.O w C.Xl a b c
  rw [← ENNReal.toReal_add (C.dl_ne_top ha hb) (C.dl_ne_top hb hc)]
  exact (ENNReal.toReal_le_toReal (C.dl_ne_top ha hc)
    (ENNReal.add_ne_top.mpr ⟨C.dl_ne_top ha hb, C.dl_ne_top hb hc⟩)).mpr h

/-- `d̃` is bounded by a constant on a compact subset of `U`. -/
theorem exists_gauge_bound {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ R : ℝ, ∀ η ∈ L, ∀ ξ ∈ L, kgauge C.G (C.Θ η ξ) ≤ R := by
  have hc : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      kgauge C.G (C.Θ z.1 z.2)) (L ×ˢ L) :=
    (G2.continuous_gauge C.G).comp_continuousOn
      (C.theta_continuousOn.mono (Set.prod_mono hLU hLU))
  obtain ⟨R, hR⟩ := (hL.prod hL).exists_bound_of_continuousOn hc
  refine ⟨R, fun η hη ξ hξ => ?_⟩
  have := hR (η, ξ) ⟨hη, hξ⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

end LiftedChart
end RothschildStein.P1
