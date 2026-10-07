-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledTransport
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- Vector-valued displacement estimate for an absolutely continuous
curve with an a.e. bounded actual derivative. Coordinate FTC avoids assuming
an unprovided vector-valued absolute-continuity API (BB Prop 1.36, p. 19). -/
theorem absolutelyContinuous_norm_sub_le {n : ℕ} {γ β : ℝ → (Fin n → ℝ)}
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hd : ∀ᵐ t ∂(volume.restrict (Icc a b)), HasDerivAt γ (β t) t ∧ ‖β t‖ ≤ C) :
    ‖γ b - γ a‖ ≤ C * |b - a| := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (abs_nonneg _))).mpr
  intro j
  have hjac : AbsolutelyContinuousOnInterval (fun t => γ t j) a b :=
    absolutelyContinuousOnInterval_comp_contDiffOn isOpen_univ
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn hac
      (mapsTo_univ _ _)
  have hd' := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hm : ‖∫ t in a..b, deriv (fun v => γ v j) t‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [hd'] with t ht htime
    have hI : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using uIoc_subset_uIcc htime
    have hder := (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (ht hI).1
    have hder' : HasDerivAt (fun v => γ v j) (β t j) t := hder
    rw [hder'.deriv]
    exact (norm_le_pi_norm (β t) j).trans (ht hI).2
  simpa only [hjac.integral_deriv_eq_sub, Pi.sub_apply] using hm

/-- At parameter at most one, every positive weight has control bound
at most δ; this also covers finite weight systems beyond the drift case
(BB Def 1.38, p. 21). -/
theorem controlled_velocity_norm_le {m n : ℕ} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {a : Fin m → ℝ} {x : Fin n → ℝ}
    {δ B : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha : ∀ i, |a i| ≤ δ ^ (w i : ℕ)) (hB : ∑ i, ‖X i x‖ ≤ B) :
    ‖∑ i, a i • X i x‖ ≤ δ * B := by
  calc
    ‖∑ i, a i • X i x‖ ≤ ∑ i, ‖a i • X i x‖ := norm_sum_le _ _
    _ = ∑ i, |a i| * ‖X i x‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, δ * ‖X i x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right ((ha i).trans (pow_le_of_le_one hδ hδ1 (by have := (w i).pos; omega))) (norm_nonneg _)
    _ = δ * ∑ i, ‖X i x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ δ * B := mul_le_mul_of_nonneg_left hB hδ

/-- Controlled displacement up to any intermediate time stays bounded
by the local field bound, provided the whole initial subcurve stays in the
region where that bound holds (BB Prop 1.36, p. 19). -/
theorem controlledCurve_initial_displacement_le {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ B b : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hb : b ∈ Icc (0 : ℝ) 1)
    (hbound : ∀ t ∈ Icc 0 b, ∑ i, ‖X i (γ t)‖ ≤ B) :
    ‖γ b - γ 0‖ ≤ δ * B * b := by
  obtain ⟨a, hmeas, ha⟩ := hγ.2.2.2
  have hsub : Icc (0 : ℝ) b ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hb.2
  have hae := ae_restrict_of_ae_restrict_of_subset hsub ha
  have hm := absolutelyContinuous_norm_sub_le hb.1 (mul_nonneg hγ.1.le hB)
    (hγ.2.1.mono (by simpa only [uIcc_of_le hb.1, uIcc_of_le zero_le_one] using hsub))
    (γ := γ) (β := fun t => ∑ i, a i t • X i (γ t))
    (by
      filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with t ht htime
      exact ⟨ht.2, controlled_velocity_norm_le hγ.1.le hδ1 ht.1 (hbound t htime)⟩)
  simpa only [sub_zero, abs_of_nonneg hb.1] using hm

end RothschildStein.G1
