-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesChart
public import RothschildStein.G1.LocalDistanceLower

/-!
# Hölder interpolation: Euclidean versus control distance

On a compact subset `K` of the lifted coordinate neighborhood, the Euclidean distance is bounded
by a constant times the lifted control distance: `‖y - x‖ ≤ C_E d̃(x, y)` for `x, y ∈ K`. Near the
diagonal this is the linear lower bound for the control distance (the fields are bounded near `K`); far from the
diagonal `d̃` is bounded below by a positive constant while `‖y - x‖` is bounded on `K`.
It converts a Euclidean Lipschitz bound of a smooth kernel into a Lipschitz bound for `d̃`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
open scoped BigOperators ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- **Euclidean distance is dominated by the control distance** on a compact subset of the
chart domain (weights at most two): `‖y - x‖ ≤ C_E d̃(x, y)`. -/
theorem exists_norm_le_mul_dl (C : LiftedChart w s Ω hΩ X x₀ m)
    (hw : ∀ i, (w i : ℕ) ≤ 2) {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ CE : ℝ, 0 < CE ∧ ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ ≤ CE * (C.dl x y).toReal := by
  have hO : IsOpen C.O := hΩ.preimage (continuous_pi fun j => continuous_apply (Fin.castAdd m j))
  have hKO : K ⊆ C.O := hKU.trans C.U_subset_O
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open hO hKO
  have hKR : IsCompact (Metric.cthickening R K) := hK.cthickening
  have hXc : ContinuousOn (fun z => ∑ i, ‖C.Xl i z‖) (Metric.cthickening R K) :=
    continuousOn_finsetSum _ fun i _ =>
      (((C.lift_smooth i).continuousOn).mono hRK).norm
  obtain ⟨B₀, hB₀⟩ := hKR.exists_bound_of_continuousOn hXc
  set B : ℝ := max B₀ 1 with hBdef
  have hB : 0 < B := lt_max_of_lt_right one_pos
  have hbound : ∀ x ∈ K, ∀ z : Fin (n + m) → ℝ, ‖z - x‖ ≤ R → ∑ i, ‖C.Xl i z‖ ≤ B := by
    intro x hx z hz
    have hzR : z ∈ Metric.cthickening R K :=
      Metric.mem_cthickening_of_dist_le z x R K hx (by rwa [dist_eq_norm])
    exact (le_abs_self _).trans ((hB₀ z hzR).trans (le_max_left _ _))
  obtain ⟨Dk, hDk⟩ := hK.isBounded.exists_norm_le
  set D : ℝ := 2 * max Dk 0 + 1 with hD
  have hD0 : 0 < D := by positivity
  have hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ ≤ D := by
    intro x hx y hy
    have h1 := hDk x hx
    have h2 := hDk y hy
    have : max Dk 0 ≥ Dk := le_max_left _ _
    have : max Dk 0 ≥ 0 := le_max_right _ _
    calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ D := by rw [hD]; linarith
  set c₀ : ℝ := min 1 (min (R / B) (min B R / B)) with hc₀
  have hc₀0 : 0 < c₀ := lt_min one_pos (lt_min (div_pos hR hB) (div_pos (lt_min hB hR) hB))
  refine ⟨max B (D / c₀), lt_max_of_lt_left hB, fun x hx y hy => ?_⟩
  have hdl : C.dl x y ≠ ⊤ := C.dl_ne_top (hKU hx) (hKU hy)
  have hdl0 : 0 ≤ (C.dl x y).toReal := ENNReal.toReal_nonneg
  by_cases hnear : ‖y - x‖ ≤ min B R
  · have h := G1.controlDistance_linear_lower_bound (Ω := C.O) hw x y hB hR (hbound x hx) hnear
    have h2 : ‖y - x‖ / B ≤ (C.dl x y).toReal := (ENNReal.ofReal_le_iff_le_toReal hdl).mp h
    calc ‖y - x‖ = B * (‖y - x‖ / B) := by field_simp
      _ ≤ B * (C.dl x y).toReal := mul_le_mul_of_nonneg_left h2 hB.le
      _ ≤ max B (D / c₀) * (C.dl x y).toReal :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hdl0
  · have hfar := not_le.mp hnear
    have h := G1.controlDistance_lower_bound_of_buffer (Ω := C.O) hw x y hB hR (hbound x hx)
    have h2 : min 1 (min (R / B) (‖y - x‖ / B)) ≤ (C.dl x y).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hdl).mp h
    have h3 : c₀ ≤ min 1 (min (R / B) (‖y - x‖ / B)) := by
      refine min_le_min le_rfl (min_le_min le_rfl ?_)
      exact div_le_div_of_nonneg_right hfar.le hB.le
    have h4 : c₀ ≤ (C.dl x y).toReal := h3.trans h2
    have h5 : ‖y - x‖ ≤ D := hdiam x hx y hy
    calc ‖y - x‖ ≤ D := h5
      _ = D / c₀ * c₀ := by field_simp
      _ ≤ D / c₀ * (C.dl x y).toReal := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ max B (D / c₀) * (C.dl x y).toReal :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hdl0

end RothschildStein.P2
