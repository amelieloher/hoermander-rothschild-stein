-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalCurve
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Affine changes of parameter for horizontal curves and control lengths. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal
namespace HeatKernel

/-- Multiplying all controls multiplies their Euclidean norm by the absolute value. -/
theorem controlNorm_mul {q : ℕ} (a : Fin q → ℝ → ℝ) (c u : ℝ) :
    controlNorm (fun i v => c * a i v) u = |c| * controlNorm a u := by
  simp only [controlNorm, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Restriction to a smaller ordered interval preserves horizontality. -/
theorem IsHorizontalCurveOn.mono {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t u v : ℝ} (h : IsHorizontalCurveOn X γ a s t)
    (hst : s ≤ t) (huv : u ≤ v) (hsub : Icc u v ⊆ Icc s t) :
    IsHorizontalCurveOn X γ a u v := by
  exact ⟨h.absolutelyContinuous.mono (by simpa only [uIcc_of_le hst, uIcc_of_le huv] using hsub),
    fun i => (h.aemeasurable i).mono_measure (Measure.restrict_mono hsub le_rfl),
    h.integrable_norm.mono_set hsub,
    Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)) h.hasDerivAt⟩

/-- A positive affine parameter map takes the unit interval to the given interval. -/
theorem mapsTo_affine_unit {s t : ℝ} (hst : s ≤ t) :
    MapsTo (fun u : ℝ => s + (t - s) * u) (Icc 0 1) (Icc s t) := by
  intro u hu
  constructor <;> nlinarith [hu.1, hu.2]

/-- Positive affine normalization of a horizontal curve onto the unit interval. -/
theorem IsHorizontalCurveOn.affine_unit {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} (h : IsHorizontalCurveOn X γ a s t)
    (hst : s < t) :
    IsHorizontalCurveOn X (fun u => γ (s + (t - s) * u))
      (fun i u => (t - s) * a i (s + (t - s) * u)) 0 1 := by
  let c := t - s
  have hc : 0 < c := sub_pos.mpr hst
  have hm := mapsTo_affine_unit hst.le
  have hq : QuasiMeasurePreserving (fun u : ℝ => s + c * u)
      (volume.restrict (Icc 0 1)) (volume.restrict (Icc s t)) :=
    ((measurePreserving_add_left volume s).quasiMeasurePreserving.comp
      (by simpa only [smul_eq_mul] using
        (quasiMeasurePreserving_smul (E := ℝ) volume hc.ne'))).restrict hm
  have hK : LipschitzOnWith (⟨c, hc.le⟩ : ℝ≥0) (fun u : ℝ => s + c * u) (uIcc 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u _ v _
    simp only [Real.dist_eq]
    rw [show s + c * u - (s + c * v) = c * (u - v) by ring, abs_mul,
      abs_of_pos hc]
    exact le_rfl
  refine ⟨absolutelyContinuousOnInterval_comp_of_monotone h.absolutelyContinuous
    (Or.inl (by intro u v huv; dsimp; nlinarith)) hK
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le hst.le] using hm),
    fun i => aemeasurable_const.mul ((h.aemeasurable i).comp_quasiMeasurePreserving hq), ?_, ?_⟩
  · have hi : IntervalIntegrable (controlNorm a) volume s t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hst.le).2 h.integrable_norm
    have hj := (hi.comp_add_left s).comp_mul_left (c := c)
    have hj' : IntervalIntegrable (fun u => controlNorm a (s + c * u)) volume 0 1 := by
      simpa only [sub_self, zero_div, div_self hc.ne', c] using hj
    have hk := hj'.const_mul c
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).1
    convert hk using 1
    funext u
    rw [controlNorm_mul, abs_of_pos hc]
    rfl
  · filter_upwards [hq.ae h.hasDerivAt] with u hu
    have hd := hu.scomp u (((hasDerivAt_id u).const_mul c).const_add s)
    simpa only [Function.comp_def, id_eq, mul_one, Finset.smul_sum, smul_smul, c] using hd

/-- Affine normalization preserves the control length. -/
theorem controlLength_affine_unit {q : ℕ} (a : Fin q → ℝ → ℝ) {s t : ℝ} (hst : s < t) :
    (∫ u in Icc (0 : ℝ) 1, controlNorm (fun i v => (t - s) * a i (s + (t - s) * v)) u) =
      ∫ u in Icc s t, controlNorm a u := by
  have hc : 0 < t - s := sub_pos.mpr hst
  simp_rw [controlNorm_mul, abs_of_pos hc]
  change (∫ u in Icc (0 : ℝ) 1, (t - s) * controlNorm a (s + (t - s) * u)) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_const_mul]
  have he := intervalIntegral.smul_integral_comp_mul_add (controlNorm a) (t - s) s
    (a := (0 : ℝ)) (b := 1)
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel,
    add_comm s, intervalIntegral.integral_of_le hst.le, integral_Icc_eq_integral_Ioc] using he

/-- The distance between endpoints of a horizontal sub-arc is bounded by its length. -/
theorem IsHorizontalCurveOn.distance_le_controlLength {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} (h : IsHorizontalCurveOn X γ a s t) (hst : s ≤ t) :
    horizontalL2Distance X (γ s) (γ t) ≤ ENNReal.ofReal (∫ u in Icc s t, controlNorm a u) := by
  rcases hst.eq_or_lt with he | he
  · subst t
    simp
  · have hb := horizontalL2Distance_le_controlLength (h.affine_unit he)
    rw [controlLength_affine_unit a he] at hb
    simpa only [mul_zero, add_zero, mul_one, add_sub_cancel] using hb

/-- Every ordered sub-arc has endpoint distance at most its integrated control norm. -/
theorem IsHorizontalCurveOn.subarc_distance_le {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {u v s t : ℝ} (h : IsHorizontalCurveOn X γ a u v)
    (hus : u ≤ s) (hst : s ≤ t) (htv : t ≤ v) :
    horizontalL2Distance X (γ s) (γ t) ≤ ENNReal.ofReal (∫ r in Icc s t, controlNorm a r) := by
  apply (h.mono (hus.trans (hst.trans htv)) hst ?_).distance_le_controlLength hst
  intro r hr
  exact ⟨hus.trans hr.1, hr.2.trans htv⟩

end HeatKernel
