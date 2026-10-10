-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.BoundedHeatOperators

/-! # The scaled resolvent multiplier equation

Functional calculus turns the scalar rational identity into the bounded operator equation
used to identify a scaled form resolvent.
-/

@[expose] public section
noncomputable section
open Set
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem denominator_mul_resolventMultiplier {scale r : ℝ} (hscale : 0 < scale)
    (hr : r ∈ Icc (0 : ℝ) 1) :
    (r + scale * (1 - r)) * resolventMultiplier scale r = r := by
  have hd := (resolventMultiplier_denominator_pos hscale hr).ne'
  unfold resolventMultiplier
  field_simp [hd]

/-- The rational multiplier of a scaled resolvent. -/
def scaledResolventCfcOperator (R : E →L[ℂ] E) (scale : ℝ) : E →L[ℂ] E :=
  cfc (resolventMultiplier scale) R

theorem cfc_resolvent_denominator (R : E →L[ℂ] E) (hR : IsSelfAdjoint R) (scale : ℝ) :
    (cfc (fun r : ℝ => r + scale * (1 - r)) R : E →L[ℂ] E) = R + scale • (1 - R) := by
  have hc : ContinuousOn (fun r : ℝ => 1 - r) (spectrum ℝ R) :=
    (continuous_const.sub continuous_id).continuousOn
  have hs : (cfc (fun r : ℝ => scale * (1 - r)) R : E →L[ℂ] E) =
      scale • cfc (fun r : ℝ => 1 - r) R := by
    simpa only [smul_eq_mul] using cfc_smul scale (fun r : ℝ => 1 - r) R hc
  rw [cfc_add R (fun r : ℝ => r) (fun r : ℝ => scale * (1 - r))
      continuous_id.continuousOn (hc.const_smul scale),
    hs,
    cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) R
      continuous_const.continuousOn continuous_id.continuousOn,
    cfc_id' ℝ R hR, cfc_const_one ℝ R hR]

theorem scaledResolventCfcOperator_equation (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (scale : ℝ) (hscale : 0 < scale) :
    (R + scale • (1 - R)) * scaledResolventCfcOperator R scale = R := by
  have hd : ContinuousOn (fun r : ℝ => r + scale * (1 - r)) (spectrum ℝ R) :=
    (continuous_id.add (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hg := (continuousOn_resolventMultiplier hscale).mono hspec
  have hc := cfc_mul (fun r : ℝ => r + scale * (1 - r)) (resolventMultiplier scale) R hd hg
  rw [cfc_resolvent_denominator R hR scale] at hc
  calc
    _ = cfc (fun r : ℝ => (r + scale * (1 - r)) * resolventMultiplier scale r) R := hc.symm
    _ = cfc (fun r : ℝ => r) R := cfc_congr (fun r hr => denominator_mul_resolventMultiplier hscale (hspec hr))
    _ = R := cfc_id' ℝ R hR

end HeatKernel
