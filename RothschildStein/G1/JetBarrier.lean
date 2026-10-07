-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.VariationBounds
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- A derivative bound valid inside the radius-two ball keeps a curve
inside that ball for the explicit short time. This first-exit estimate is the
finite-jet bootstrap in (BB Prop 1.2, p. 3). -/
theorem norm_lt_two_of_deriv_bound_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {t C : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hd : ∀ v ∈ Icc 0 t, HasDerivAt f (g v) v)
    (hb : ∀ v ∈ Icc 0 t, ‖f v‖ ≤ 2 → ‖g v‖ ≤ C)
    (hzero : ‖f 0‖ ≤ 1) (hsmall : C * t < 1) : ‖f t‖ < 2 := by
  by_contra hbad
  have hf : ContinuousOn f (Icc 0 t) := fun v hv => (hd v hv).continuousAt.continuousWithinAt
  have hext : ∃ v ∈ Icc 0 t, ‖f v‖ = 2 :=
    intermediate_value_Icc ht hf.norm ⟨by linarith, le_of_not_gt hbad⟩
  let S : Set ℝ := Icc 0 t ∩ (fun v => ‖f v‖) ⁻¹' {2}
  have hclosed : IsClosed S := hf.norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨b, hbS, hmin⟩ := hcompact.exists_isMinOn
    (by obtain ⟨v, hv, he⟩ := hext; exact ⟨v, hv, he⟩) continuousOn_id
  have htimeb : b ∈ Icc 0 t := hbS.1
  have hfb : ‖f b‖ = 2 := hbS.2
  have hbefore : ∀ v ∈ Ico 0 b, ‖f v‖ ≤ 2 := by
    intro v hv
    by_contra hgreater
    have hv' : v ∈ Icc 0 t := ⟨hv.1, hv.2.le.trans htimeb.2⟩
    obtain ⟨w, hw, hwf⟩ := intermediate_value_Icc hv.1
      (hf.norm.mono (Icc_subset_Icc le_rfl hv'.2))
      (show (2 : ℝ) ∈ Icc ‖f 0‖ ‖f v‖ from ⟨by linarith, le_of_not_ge hgreater⟩)
    have hwb : b ≤ w := hmin ⟨⟨hw.1, hw.2.trans hv'.2⟩, hwf⟩
    linarith [hw.2, hv.2]
  have hdisp := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun v hv => (hd v ⟨hv.1, hv.2.trans htimeb.2⟩).hasDerivWithinAt)
    (fun v hv => hb v ⟨hv.1, hv.2.le.trans htimeb.2⟩ (hbefore v hv))
    b (show b ∈ Icc 0 b from ⟨htimeb.1, le_rfl⟩)
  have htri : ‖f b‖ ≤ ‖f b - f 0‖ + ‖f 0‖ := by
    calc
      ‖f b‖ = ‖(f b - f 0) + f 0‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hmul : C * b ≤ C * t := mul_le_mul_of_nonneg_left htimeb.2 hC
  simp only [sub_zero] at hdisp
  linarith

/-- The finite-jet first-exit estimate for either time orientation
(BB Prop 1.2, p. 3). -/
theorem norm_lt_two_of_deriv_bound_uIcc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : ℝ → E} {t C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ v ∈ uIcc 0 t, HasDerivAt f (g v) v)
    (hb : ∀ v ∈ uIcc 0 t, ‖f v‖ ≤ 2 → ‖g v‖ ≤ C)
    (hzero : ‖f 0‖ ≤ 1) (hsmall : C * |t| < 1) : ‖f t‖ < 2 := by
  rcases le_total 0 t with ht | ht
  · exact norm_lt_two_of_deriv_bound_Icc ht hC
      (fun v hv => hd v (by simpa only [uIcc_of_le ht] using hv))
      (fun v hv => hb v (by simpa only [uIcc_of_le ht] using hv)) hzero
      (by simpa only [abs_of_nonneg ht] using hsmall)
  · have hsub : ∀ v ∈ Icc 0 (-t), -v ∈ uIcc 0 t := by
      intro v hv
      rw [uIcc_of_ge ht]
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have hd' : ∀ v ∈ Icc 0 (-t), HasDerivAt (fun w => f (-w)) (-g (-v)) v := by
      intro v hv
      simpa only [Function.comp_def, neg_one_smul] using
        (hd (-v) (hsub v hv)).scomp v (hasDerivAt_neg v)
    have h := norm_lt_two_of_deriv_bound_Icc (neg_nonneg.mpr ht) hC hd'
      (fun v hv hnorm => by simpa only [norm_neg] using hb (-v) (hsub v hv) hnorm)
      (by simpa only [neg_zero] using hzero)
      (by simpa only [abs_of_nonpos ht] using hsmall)
    simpa only [neg_neg] using h

end RothschildStein.G1
