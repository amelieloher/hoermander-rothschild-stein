-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorBounds

/-!
# The restricted error: the Hölder bound without a measurability hypothesis

A function with finite `holderENorm C.dl α V f` on a subset `V` of the chart domain is continuous
for the Euclidean topology of `V` (the metric topology of `d̃` on the chart domain is the Euclidean
one, `LiftedChart.isOpen_iff_forall_carrierDist`), hence measurable on a measurable `V`. So the
Hölder bound `exists_restrictedError_holder_bound_of_aestronglyMeasurable` holds for every `f`
of finite Hölder norm.
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
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- A function of finite Hölder norm for `d̃` on a subset of the
chart domain is continuous there for the Euclidean topology (the `d̃`-topology is the Euclidean one,
`H2CertificateCarrier`). -/
theorem continuousOn_of_holderENorm_lt_top {V : Set (Fin (n + m) → ℝ)} (hVU : V ⊆ C.U) {α : ℝ}
    (hα : 0 < α) {f : (Fin (n + m) → ℝ) → ℝ} (hf : holderENorm C.dl α V f < ⊤) :
    ContinuousOn f V := by
  have hsemi : holderSeminorm C.dl α V f < ⊤ := lt_of_le_of_lt le_add_self hf
  obtain ⟨C₀, ⟨hC₀top, hC₀⟩, -⟩ := sInf_lt_iff.mp hsemi
  set c : ℝ := C₀.toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hHol : ∀ x ∈ V, ∀ y ∈ V, |f x - f y| ≤ c * (C.dl x y).toReal ^ α := by
    intro x hx y hy
    have hfin : C.dl x y ≠ ⊤ := C.dl_finite_on_U (hVU hx) (hVU hy)
    have h := hC₀ x hx y hy hfin.lt_top
    have e : C₀ * C.dl x y ^ α = ENNReal.ofReal (c * (C.dl x y).toReal ^ α) := by
      rw [ENNReal.ofReal_mul hc0, hc, ENNReal.ofReal_toReal hC₀top.ne,
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα.le, ENNReal.ofReal_toReal hfin]
    rw [e] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hδ₀ : 0 < (ε / (c + 1)) ^ (1 / α) := by positivity
  set δ₀ : ℝ := (ε / (c + 1)) ^ (1 / α) with hδ₀def
  have hkey : ∀ t : ℝ, 0 ≤ t → t < δ₀ → c * t ^ α < ε := by
    intro t ht0 ht
    have h1 : t ^ α < δ₀ ^ α := Real.rpow_lt_rpow ht0 ht hα
    have h2 : δ₀ ^ α = ε / (c + 1) := by
      rw [hδ₀def, ← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
    rw [h2] at h1
    calc c * t ^ α ≤ (c + 1) * t ^ α := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < (c + 1) * (ε / (c + 1)) := mul_lt_mul_of_pos_left h1 (by positivity)
      _ = ε := by field_simp
  have hxU : x ∈ C.U := hVU hx
  have hBopen : IsOpen (Carrier.val '' (Metric.ball (Carrier.mk x hxU) δ₀)) :=
    Carrier.isOpenEmbedding_val.isOpenMap _ Metric.isOpen_ball
  have hxB : x ∈ Carrier.val '' (Metric.ball (Carrier.mk x hxU) δ₀) :=
    ⟨Carrier.mk x hxU, Metric.mem_ball_self hδ₀, rfl⟩
  obtain ⟨ε', hε', hsub⟩ := Metric.isOpen_iff.mp hBopen x hxB
  refine ⟨ε', hε', fun {y} hyV hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hsub (Metric.mem_ball.mpr hy)
  have hd : (C.dl x y).toReal < δ₀ := by
    have := Metric.mem_ball.mp hz
    rw [Carrier.dist_def] at this
    rw [← hzy, show C.dl x z.val = C.dl z.val x from G1.controlDistance_symm C.O w C.Xl x z.val]
    exact this
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hHol x hx y hyV) (hkey _ ENNReal.toReal_nonneg hd)

/-- A function of finite Hölder norm for `d̃` on a measurable
subset of the chart domain is measurable there. -/
theorem aestronglyMeasurable_of_holderENorm_lt_top {V : Set (Fin (n + m) → ℝ)} (hVU : V ⊆ C.U)
    (hVm : MeasurableSet V) {α : ℝ} (hα : 0 < α) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α V f < ⊤) : AEStronglyMeasurable f (volume.restrict V) :=
  (continuousOn_of_holderENorm_lt_top hVU hα hf).aestronglyMeasurable hVm

variable {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}
  {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}

/-- **The Hölder bound for the restricted error**: for
`0 < α < 1` and `0 < r < r_*`, for every `f`,
`‖𝓕_r f‖_{C^α(U_r)} ≤ C_α r^(1-α) ‖f‖_{C^α(U_r)}` in `holderENorm` with `C.dl`, where
`U_r = rsBall C.O w C.Xl ξ₀ r` and `C_α` is independent of `r` and `f`. -/
theorem exists_restrictedError_holder_bound (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ r : ℝ, 0 < r → r < rstar → ∀ f : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) (C.restrictedError ξ₀ r kk f) ≤
        ENNReal.ofReal (CH * r ^ (1 - α)) *
          holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) f := by
  obtain ⟨CH, hCH, hbound⟩ := exists_restrictedError_holder_bound_of_aestronglyMeasurable hr hk hα0 hα1
  refine ⟨CH, hCH, fun r hr0 hrr f => ?_⟩
  by_cases hH : holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) f = ⊤
  · rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.mpr
      (mul_pos hCH (Real.rpow_pos_of_pos hr0 _))).ne']
    exact le_top
  · have hSU : rsBall C.O w C.Xl ξ₀ r ⊆ C.U := fun y hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)
    obtain ⟨Cv, hCv, hsetup⟩ := hr.exists_setup hk
    have hSm := (hsetup r hr0 hrr).1.measurableSet
    exact hbound r hr0 hrr f
      (aestronglyMeasurable_of_holderENorm_lt_top hSU hSm hα0 (lt_top_iff_ne_top.mpr hH))

end LiftedChart

end RothschildStein.P1
