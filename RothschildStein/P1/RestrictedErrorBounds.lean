-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorDef
public import RothschildStein.Definitions.holderENorm

/-!
# The restricted error of the right parametrix: sup and Hölder bounds

Continuation of `RestrictedError`: the sup bound `‖𝓕_r f‖_∞ ≤ C r ‖f‖_∞` and the Hölder bound
`‖𝓕_r f‖_{C^α(U_r)} ≤ C_α r^(1-α) ‖f‖_{C^α(U_r)}` in terms of `holderENorm` (with
the lifted control distance `C.dl`), for `0 < r < r_*` (BB pp. 606–607).
The Hölder bound only uses the sup norm of `f` on the right-hand side.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
  {rstar r : ℝ} {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}

/-- **The Hölder bound for the restricted error**: for `0 < α < 1`,
`0 < r < r_*` and `f` measurable on `U_r`,
`‖𝓕_r f‖_{C^α(U_r)} ≤ C_α r^(1-α) ‖f‖_{C^α(U_r)}` in `holderENorm` with `C.dl`. The
constant `C_α` depends on `A`, `B`, the volume constant, the homogeneous dimension and `α` only,
not on `r` and `f`. (Split at `2h`: near integrals `O(h)`, far dyadic shells `O(h)` each, at most
`C + log₂ (r/h)` of them; then `z^(1-α)(1 + |log z|)` is bounded.) -/
theorem exists_restrictedError_holder_bound_of_aestronglyMeasurable (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ r : ℝ, 0 < r → r < rstar → ∀ f : (Fin (n + m) → ℝ) → ℝ,
      AEStronglyMeasurable f (volume.restrict (rsBall C.O w C.Xl ξ₀ r)) →
      holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) (C.restrictedError ξ₀ r kk f) ≤
        ENNReal.ofReal (CH * r ^ (1 - α)) *
          holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) f := by
  obtain ⟨Cv, hCv, hsetup⟩ := hr.exists_setup hk
  have hA := hk.A_nonneg
  have hB := hk.B_nonneg
  have hα' : 0 < 1 - α := by linarith
  have hC₁ : 0 ≤ Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1) := by positivity
  have hCα : 0 ≤ holderConst A B Cv (C.G.homogeneousDimension - 1) α := by
    unfold holderConst
    positivity
  refine ⟨2 * A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) +
    holderConst A B Cv (C.G.homogeneousDimension - 1) α + 1, by positivity, fun r hr0 hrr f hf => ?_⟩
  obtain ⟨hshell, hsb, hnull⟩ := hsetup r hr0 hrr
  set S := rsBall C.O w C.Xl ξ₀ r with hS
  set F := C.restrictedError ξ₀ r kk f with hF
  set C₁ : ℝ := Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1) with hC₁def
  set Cα : ℝ := holderConst A B Cv (C.G.homogeneousDimension - 1) α with hCαdef
  have hrpos : 0 < r ^ (1 - α) := Real.rpow_pos_of_pos hr0 _
  have hCHpos : 0 < (2 * A * C₁ + Cα + 1) * r ^ (1 - α) := by positivity
  by_cases hH : holderENorm C.dl α S f = ⊤
  · rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCHpos).ne']
    exact le_top
  · have hsup_fin : (⨆ x : S, ENNReal.ofReal |f x|) ≠ ⊤ :=
      ne_top_of_le_ne_top hH (le_self_add (b := holderSeminorm C.dl α S f))
    set M : ℝ := (⨆ x : S, ENNReal.ofReal |f x|).toReal with hMdef
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hM : ∀ y ∈ S, |f y| ≤ M := fun y hy =>
      (ENNReal.ofReal_le_iff_le_toReal hsup_fin).mp
        (le_iSup (fun x : S => ENNReal.ofReal |f x|) ⟨y, hy⟩)
    have hMe : ENNReal.ofReal M = ⨆ x : S, ENNReal.ofReal |f x| := ENNReal.ofReal_toReal hsup_fin
    have hFeq : ∀ x ∈ S, F x = ∫ y in S, sliceKernel S kk x y * f y :=
      fun x hx => restrictedError_eq hshell.measurableSet hx (hnull x hx)
    have hsup : (⨆ x : S, ENNReal.ofReal |F x|) ≤ ENNReal.ofReal (2 * A * C₁ * r * M) := by
      refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
      rw [hFeq x x.2]
      calc _ ≤ A * M * C₁ * (2 * r) := hsb.abs_integral_le hshell hM0 hM x.2
        _ = 2 * A * C₁ * r * M := by ring
    have hsemi : holderSeminorm C.dl α S F ≤ ENNReal.ofReal (Cα * r ^ (1 - α) * M) := by
      refine sInf_le ⟨ENNReal.ofReal_lt_top, fun x hx y hy hxy => ?_⟩
      have hb := hsb.abs_sub_le_holder hshell hf hM0 hM hα0 hα1 hx hy
      rw [hFeq x hx, hFeq y hy]
      calc _ ≤ ENNReal.ofReal (Cα * r ^ (1 - α) * M * (C.dl x y).toReal ^ α) :=
            ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal (Cα * r ^ (1 - α) * M) * ENNReal.ofReal ((C.dl x y).toReal ^ α) :=
            ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (Cα * r ^ (1 - α) * M) * C.dl x y ^ α := by
            rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα0.le,
              ENNReal.ofReal_toReal hxy.ne]
    have hr1 : r ≤ 1 := hrr.le.trans hr.le_one
    have hr_le : r ≤ r ^ (1 - α) := by
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (1 - α) := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by linarith)
    have h1 : 2 * A * C₁ * r * M ≤ 2 * A * C₁ * r ^ (1 - α) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr_le (by positivity)) hM0
    calc holderENorm C.dl α S F
        = (⨆ x : S, ENNReal.ofReal |F x|) + holderSeminorm C.dl α S F := rfl
      _ ≤ ENNReal.ofReal (2 * A * C₁ * r * M) + ENNReal.ofReal (Cα * r ^ (1 - α) * M) :=
          add_le_add hsup hsemi
      _ = ENNReal.ofReal (2 * A * C₁ * r * M + Cα * r ^ (1 - α) * M) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal ((2 * A * C₁ + Cα + 1) * r ^ (1 - α) * M) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [mul_nonneg hrpos.le hM0]
      _ = ENNReal.ofReal ((2 * A * C₁ + Cα + 1) * r ^ (1 - α)) * ENNReal.ofReal M :=
          ENNReal.ofReal_mul hCHpos.le
      _ ≤ ENNReal.ofReal ((2 * A * C₁ + Cα + 1) * r ^ (1 - α)) * holderENorm C.dl α S f := by
          gcongr
          rw [hMe]
          exact le_self_add

end LiftedChart

end RothschildStein.P1
