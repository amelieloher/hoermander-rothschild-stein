-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowVariational
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Gronwall bound on a closed forward interval, using an actual derivative
and a homogeneous derivative bound (BB Prop 1.2, p. 3). -/
theorem norm_le_exp_of_deriv_bound_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {t K δ : ℝ} (ht : 0 ≤ t)
    (hd : ∀ v ∈ Icc 0 t, HasDerivAt f (g v) v)
    (hbound : ∀ v ∈ Icc 0 t, ‖g v‖ ≤ K * ‖f v‖) (hzero : ‖f 0‖ ≤ δ) :
    ‖f t‖ ≤ δ * Real.exp (K * t) := by
  have hm := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0)
    (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
    (fun v hv => (hd v ⟨hv.1, hv.2.le⟩).hasDerivWithinAt)
    hzero (fun v hv => by simpa using hbound v ⟨hv.1, hv.2.le⟩)
    t (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  simpa only [gronwallBound_ε0, sub_zero] using hm

/-- The same Gronwall bound for either sign of time; no sign change is
lost in the time reversal (BB Prop 1.2, p. 3). -/
theorem norm_le_exp_of_deriv_bound_uIcc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {t K δ : ℝ}
    (hd : ∀ v ∈ uIcc 0 t, HasDerivAt f (g v) v)
    (hbound : ∀ v ∈ uIcc 0 t, ‖g v‖ ≤ K * ‖f v‖) (hzero : ‖f 0‖ ≤ δ) :
    ‖f t‖ ≤ δ * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_le_exp_of_deriv_bound_Icc ht
      (fun v hv => hd v (by simpa only [uIcc_of_le ht] using hv))
      (fun v hv => hbound v (by simpa only [uIcc_of_le ht] using hv)) hzero
  · have hsub : ∀ v ∈ Icc 0 (-t), -v ∈ uIcc 0 t := by
      intro v hv
      rw [uIcc_of_ge ht]
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have hneg : ∀ v ∈ Icc 0 (-t), HasDerivAt (fun w => f (-w)) (-g (-v)) v := by
      intro v hv
      simpa only [Function.comp_def, neg_one_smul] using
        (hd (-v) (hsub v hv)).scomp v (hasDerivAt_neg v)
    have hm := norm_le_exp_of_deriv_bound_Icc (neg_nonneg.mpr ht) hneg
      (fun v hv => by simpa only [norm_neg] using hbound (-v) (hsub v hv))
      (by simpa only [neg_zero] using hzero)
    simpa only [neg_neg, abs_of_nonpos ht] using hm

/-- Under joint smoothness: the spatial flow derivative is
bounded solely by the first coefficient jet and elapsed time (BB p. 3).
The bound is an operator norm, including the zero-dimensional case. -/
theorem localFlow_spatial_derivative_bound_of_joint_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω U : Set E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : (E × ℝ) → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : E} (hx : x ∈ U) {t K : ℝ} (ht : t ∈ Ioo (-τ) τ) (_hK : 0 ≤ K)
    (hbound : ∀ v ∈ uIcc 0 t, ‖fderiv ℝ Z (Φ (x, v))‖ ≤ K) :
    ‖fderiv ℝ (fun y => Φ (y, t)) x‖ ≤ Real.exp (K * |t|) := by
  let J := fun v => fderiv ℝ (fun y => Φ (y, v)) x
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset hzero ht
  have hJ₀ : J 0 = ContinuousLinearMap.id ℝ E := by
    have heq : (fun y => Φ (y, 0)) =ᶠ[𝓝 x] id := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hΦ y hy).1
    exact heq.fderiv_eq.trans fderiv_id
  have hm := norm_le_exp_of_deriv_bound_uIcc
    (fun v hv => localFlow_variational_of_joint_contDiff hΩ hU hZ Φ hjoint
      (fun y hy => (hΦ y hy).2) hx (hsub hv))
    (fun v hv => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hbound v hv) (norm_nonneg (J v))))
    (show ‖J 0‖ ≤ 1 by rw [hJ₀]; exact ContinuousLinearMap.norm_id_le)
  simpa only [one_mul] using hm

end RothschildStein.G1
