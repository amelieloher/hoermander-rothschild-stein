-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScaledResolventCfc

/-! # Invertibility of the scaled resolvent denominator -/

@[expose] public section
noncomputable section
open Set
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem cfc_inverse_resolvent_denominator (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (scale : ℝ) (hscale : 0 < scale) :
    cfc (fun r : ℝ => (r + scale * (1 - r))⁻¹) R * (R + scale • (1 - R)) = 1 := by
  have hd : ContinuousOn (fun r : ℝ => r + scale * (1 - r)) (spectrum ℝ R) :=
    (continuous_id.add (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have hn : ∀ r ∈ spectrum ℝ R, r + scale * (1 - r) ≠ 0 :=
    fun r hr => (resolventMultiplier_denominator_pos hscale (hspec hr)).ne'
  rw [← cfc_resolvent_denominator R hR scale, ← cfc_mul (fun r : ℝ => (r + scale * (1 - r))⁻¹)
      (fun r : ℝ => r + scale * (1 - r)) R (hd.inv₀ hn) hd]
  calc
    _ = cfc (fun _ : ℝ => 1) R := cfc_congr (fun r hr => inv_mul_cancel₀ (hn r hr))
    _ = 1 := cfc_const_one ℝ R hR

theorem resolvent_denominator_injective (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) (scale : ℝ) (hscale : 0 < scale) :
    Function.Injective (fun f : E => (R + scale • (1 - R)) f) := by
  intro f g hfg
  have he := congrArg (fun x : E => (cfc (fun r : ℝ => (r + scale * (1 - r))⁻¹) R : E →L[ℂ] E) x) hfg
  simpa only [← mul_apply_eq_comp, cfc_inverse_resolvent_denominator R hR hspec scale hscale,
    one_apply_eq_self] using he

end HeatKernel
