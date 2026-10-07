-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

noncomputable section

open ContinuousLinearMap MeasureTheory Set Metric
open scoped SchwartzMap

namespace Hormander.A

/-- The canonical kernel is nonnegative. -/
theorem J_nonneg {N : ℕ} (x : Carrier N) : 0 ≤ J N x := by
  change 0 ≤ (jBump N).normed volume x
  exact ContDiffBump.nonneg_normed (jBump N) x

/-- The canonical kernel is even. -/
theorem J_even {N : ℕ} (x : Carrier N) : J N (-x) = J N x := by
  change (jBump N).normed volume (-x) = (jBump N).normed volume x
  exact ContDiffBump.normed_neg (jBump N) x

/-- The complexified kernel is even. -/
@[simp] theorem Jc_even {N : ℕ} (x : Carrier N) : Jc N (-x) = Jc N x := by
  simp [Jc_apply, J_even]

/-- Every positive dilation of the complexified kernel is even. -/
@[simp] theorem Jδ_even {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (x : Carrier N) :
    Jδ N δ hδ (-x) = Jδ N δ hδ x := by
  rw [Jδ_apply, Jδ_apply, smul_neg, Jc_even]

/-- Reflection leaves the fixed rescaled mollifier unchanged. -/
theorem reflected_Jδ_eq (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    reflectedSchwartz (Jδ N δ hδ) = Jδ N δ hδ := by
  ext x
  change Jδ N δ hδ (-x) = Jδ N δ hδ x
  exact Jδ_even (δ := δ) hδ x

/-- [BB.Def5.18] Pairing against the mollified distribution is the transposed Schwartz action. -/
@[simp] theorem Sδ_apply (N : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (T : 𝓢'(Carrier N, ℂ)) (ψ : 𝓢(Carrier N, ℂ)) :
    Sδ N δ hδ T ψ = T (SδSchwartz N δ hδ ψ) := by
  rw [Sδ, temperedConvolution_apply]
  change T (SchwartzMap.convolution (lsmul ℂ ℂ)
    (reflectedSchwartz (Jδ N δ hδ)) ψ) = T (SδSchwartz N δ hδ ψ)
  rw [reflected_Jδ_eq]
  rfl

/-- The canonical kernel has total integral one. -/
theorem J_integral_one {N : ℕ} : ∫ x : Carrier N, J N x = 1 := by
  change ∫ x : Carrier N, (jBump N).normed volume x ∂volume = 1
  exact ContDiffBump.integral_normed (jBump N)

/-- The support of the canonical kernel is contained in the closed half-radius ball. -/
theorem J_tsupport_subset_closedBall_half {N : ℕ} :
    tsupport (J N : Carrier N → ℝ) ⊆ closedBall (0 : Carrier N) (1 / 2) := by
  change tsupport ((jBump N).normed volume) ⊆ closedBall (0 : Carrier N) (1 / 2)
  rw [tsupport, ContDiffBump.support_normed_eq]
  change closure (ball (0 : Carrier N) (1 / 2)) ⊆ closedBall (0 : Carrier N) (1 / 2)
  rw [closure_ball (0 : Carrier N) (by norm_num : (1 / 2 : ℝ) ≠ 0)]

end Hormander.A
