-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ParameterizedProductSupport
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1

/-- Uniform increments follow from joint compact support
and the global Lipschitz theorem for a compact C¹ function. -/
theorem exists_parameterizedCompact_increment_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F I : E × E → E} (hF : ContDiff ℝ 1 F) (hI : Continuous I)
    (hInv : ∀ x w, I (F (x, w), w) = x) (hZero : ∀ x, F (x, 0) = x)
    {ψ η : E → ℝ} (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ)
    (hcη : ContDiff ℝ 1 η) (hsη : HasCompactSupport η) (hη0 : η 0 = 1)
    {W : Set E} (hη : ∀ w ∈ W, η w = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x w, w ∈ W → |ψ (F (x, w)) - ψ x| ≤ C * ‖w‖ := by
  let P := fun p : E × E => ψ (F p) * η p.2
  have hP : ContDiff ℝ 1 P := (hcψ.comp hF).mul (hcη.comp contDiff_snd)
  have hsP : HasCompactSupport P := hasCompactSupport_parameterizedProduct hI hInv hsψ hsη
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsP hP (by norm_num)
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro x w hw
  have h := hC.norm_sub_le (x, w) (x, 0)
  have hn : ‖(x, w) - (x, (0 : E))‖ = ‖w‖ := by simp
  change ‖ψ (F (x, w)) * η w - ψ (F (x, 0)) * η 0‖ ≤ (C : ℝ) * ‖(x, w) - (x, (0 : E))‖ at h
  rw [hη w hw, hη0, mul_one, mul_one, hZero x, hn, Real.norm_eq_abs] at h
  exact h

end RothschildStein.H1
