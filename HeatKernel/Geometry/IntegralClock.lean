-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.ClockPushforward
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue

/-! Construction of strictly increasing regularized integral clocks. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace HeatKernel

/-- Adding a positive linear function to the primitive of a nonnegative integrable
function gives an order isomorphism of the real line. -/
theorem exists_integral_orderIso {w : ℝ → ℝ} (hw : Integrable w)
    (hn : ∀ᵐ u ∂volume, 0 ≤ w u) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ ≃o ℝ, (∀ t, e t = (∫ u in (0 : ℝ)..t, w u) + ε * t) ∧
      (∀ s t, s ≤ t → ε * (t - s) ≤ e t - e s) := by
  let f : ℝ → ℝ := fun t => (∫ u in (0 : ℝ)..t, w u) + ε * t
  have hinc : ∀ s t, s ≤ t → ε * (t - s) ≤ f t - f s := by
    intro s t hst
    have hnonneg := intervalIntegral.integral_nonneg_of_ae hst hn
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hw.intervalIntegrable (a := 0) (b := s)) (hw.intervalIntegrable (a := s) (b := t))
    dsimp [f]
    linarith
  have hmono : StrictMono f := by
    intro s t hst
    have hh := hinc s t hst.le
    have hp : 0 < ε * (t - s) := mul_pos hε (sub_pos.mpr hst)
    linarith
  have hcont : Continuous f := hw.continuous_primitive 0 |>.add (continuous_const.mul continuous_id)
  let C := ∫ u : ℝ, ‖w u‖
  have hbound : ∀ t, |∫ u in (0 : ℝ)..t, w u| ≤ C := by
    intro t
    exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      (setIntegral_le_integral hw.norm (Eventually.of_forall fun u => norm_nonneg _))
  have htop : Tendsto f atTop atTop := by
    apply tendsto_atTop.2
    intro y
    apply eventually_atTop.2
    refine ⟨(y + C) / ε, fun t ht => ?_⟩
    have hmul : y + C ≤ t * ε := (div_le_iff₀ hε).mp ht
    have hb := (abs_le.mp (hbound t)).1
    dsimp [f]
    nlinarith
  have hbot : Tendsto f atBot atBot := by
    apply tendsto_atBot.2
    intro y
    apply eventually_atBot.2
    refine ⟨(y - C) / ε, fun t ht => ?_⟩
    have hmul : t * ε ≤ y - C := (le_div_iff₀ hε).mp ht
    have hb := (abs_le.mp (hbound t)).2
    dsimp [f]
    nlinarith
  let e := hmono.orderIsoOfSurjective f (hcont.surjective htop hbot)
  exact ⟨e, fun _ => rfl, hinc⟩

/-- Every nonnegative integrable density on the unit interval has a regularized
integral clock with quantitative positive increments. -/
theorem exists_regularized_integral_clock {w : ℝ → ℝ}
    (hw : IntegrableOn w (Icc 0 1))
    (hn : ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ w u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : ℝ ≃o ℝ,
      (∀ t ∈ Icc (0 : ℝ) 1, e t = ∫ u in Icc (0 : ℝ) t, w u + ε) ∧
      (∀ s t, s ≤ t → ε * (t - s) ≤ e t - e s) := by
  let W := (Icc (0 : ℝ) 1).indicator w
  have hW : Integrable W := (integrable_indicator_iff measurableSet_Icc).2 hw
  have hnW : ∀ᵐ u ∂volume, 0 ≤ W u := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hn] with u hu
    by_cases hm : u ∈ Icc (0 : ℝ) 1
    · simpa only [W, indicator_of_mem hm] using hu hm
    · simp only [W, indicator_of_notMem hm, le_refl]
  obtain ⟨e, he, hi⟩ := exists_integral_orderIso hW hnW hε
  refine ⟨e, ?_, hi⟩
  intro t ht
  rw [he]
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right ht.2
  have hEq : (∫ u in (0 : ℝ)..t, W u) = ∫ u in (0 : ℝ)..t, w u := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact indicator_of_mem (hsub (by simpa only [uIcc_of_le ht.1] using hu)) w
  rw [hEq]
  have hiw : IntervalIntegrable w volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2 (hw.mono_set hsub)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1,
    intervalIntegral.integral_add hiw intervalIntegrable_const, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul, mul_comm ε]

/-- Quantitative positive increments of an order isomorphism give a Lipschitz inverse. -/
theorem lipschitzWith_inverse_clock {e : ℝ ≃o ℝ} {ε : ℝ} (hε : 0 < ε)
    (hi : ∀ s t, s ≤ t → ε * (t - s) ≤ e t - e s) :
    LipschitzWith (⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ : ℝ≥0) e.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  wlog huv : u ≤ v generalizing u v
  · simpa only [dist_comm] using this v u (le_of_not_ge huv)
  have hst := e.symm.monotone huv
  have hh := hi (e.symm u) (e.symm v) hst
  rw [e.apply_symm_apply, e.apply_symm_apply] at hh
  simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst),
    abs_of_nonpos (sub_nonpos.mpr huv)]
  change -(e.symm u - e.symm v) ≤ ε⁻¹ * -(u - v)
  rw [inv_mul_eq_div, le_div_iff₀ hε]
  nlinarith

end HeatKernel
