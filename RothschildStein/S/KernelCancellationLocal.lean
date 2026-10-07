-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
namespace RothschildStein.S
variable {n : ℕ} {U : Set (Fin n → ℝ)} {δ : ℝ}

/-- Local continuous data suffice for an actual integrable
kernel section whenever its translated support ball stays in the domain
(BB Lemma 2.21, p. 87; domain). -/
theorem integrable_friedrichsKernel_section_of_continuousOn
    (K : BoundedFriedrichsKernel U δ) {L : Set (Fin n → ℝ)}
    {h : (Fin n → ℝ) → ℝ} (hh : ContinuousOn h L)
    {ε : ℝ} (hε : ε ∈ Ioo 0 δ) {x : Fin n → ℝ} (hx : x ∈ U)
    (hL : ∀ y ∈ closedBall (0 : Fin n → ℝ) 1, x+ε • y ∈ L) :
    Integrable (fun y => K.toFun ε x y * h (x+ε • y)) volume := by
  have ht : Continuous (fun y : Fin n → ℝ => x+ε • y) :=
    continuous_const.add (continuous_id.const_smul ε)
  have hc : ContinuousOn (fun y => K.toFun ε x y * h (x+ε • y))
      (closedBall (0 : Fin n → ℝ) 1) :=
    (K.section_smooth hε hx).continuous.continuousOn.mul (hh.comp ht.continuousOn hL)
  apply (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_left _ _).trans (K.support ε hε x hx))).mp
  exact hc.integrableOn_compact (isCompact_closedBall (0 : Fin n → ℝ) 1)

/-- The increment identity is valid for local continuous data;
all integration is confined to the translated kernel support
(BB Lemma 2.21, p. 87). -/
theorem friedrichsKernelOp_eq_increment_of_continuousOn
    (K : BoundedFriedrichsKernel U δ) (hK : HasVanishingKernelMean K)
    {L : Set (Fin n → ℝ)} {h : (Fin n → ℝ) → ℝ} (hh : ContinuousOn h L)
    {ε : ℝ} (hε : ε ∈ Ioo 0 δ) {x : Fin n → ℝ} (hx : x ∈ U)
    (hL : ∀ y ∈ closedBall (0 : Fin n → ℝ) 1, x+ε • y ∈ L) :
    friedrichsKernelOp K.toFun h ε x =
      ∫ y, K.toFun ε x y * (h (x+ε • y)-h x) := by
  unfold friedrichsKernelOp
  simp only [mul_sub]
  rw [integral_sub (integrable_friedrichsKernel_section_of_continuousOn K hh hε hx hL)
    ((K.section_integrable hε hx).mul_const (h x)),integral_mul_const,
    hK ε hε x hx,MulZeroClass.zero_mul,sub_zero]

end RothschildStein.S
