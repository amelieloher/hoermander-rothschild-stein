-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PuncturedKernelCutoff
public import RothschildStein.H1.FieldSubtractConstant
public import RothschildStein.G2.Gauge
public import RothschildStein.H1.ContinuousPuncturedCutoff
public import RothschildStein.S.ClassicalWords
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The scalar obtained from the two cutoff limits is
exactly the source coefficient, the ball integral of Y(fθ), θ=1−η. -/
theorem criticalCutoffCoefficient_eq_ballIntegral
    {ν f η : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R : ℝ} (hηout : ∀ w, R ≤ ν w → η w = 0) :
    (∫ w in {w | ν w ≤ R}, fieldDerivative V f w * (1 - η w)) -
      (∫ w, f w * fieldDerivative V η w) =
      ∫ w in {w | ν w ≤ R}, fieldDerivative V (fun v => f v * (1 - η v)) w := by
  have heθ : (fun w => 1 - η w) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    filter_upwards [heη] with w hw
    rw [hw, sub_self]
  have hcθ : ContDiff ℝ 1 (fun w => 1 - η w) := (contDiff_const.sub hη).of_le (by simp)
  have hF : ContinuousOn (fieldDerivative V f) {(0 : Fin N → ℝ)}ᶜ :=
    (hf.continuousOn_fderiv_of_isOpen isOpen_compl_singleton (by norm_num)).clm_apply hV.continuous.continuousOn
  have hiA : IntegrableOn (fun w => fieldDerivative V f w * (1 - η w)) {w | ν w ≤ R} volume :=
    (continuous_puncturedKernel_mul_cutoff hF hcθ.continuous heθ).continuousOn.integrableOn_compact
      (G2.isCompact_gauge_le hν R)
  have hiB := integrable_mul_fieldDerivative_cutoff V hV hf.continuousOn hη hsη heη
  have hsupport : tsupport η ⊆ {w | ν w ≤ R} := by
    apply closure_minimal
    · intro w hw
      by_contra hn
      have hlt : R < ν w := lt_of_not_ge hn
      exact hw (hηout w hlt.le)
    · exact isClosed_le hν.1 continuous_const
  have hzero (w : Fin N → ℝ) (hw : w ∉ {w | ν w ≤ R}) : f w * fieldDerivative V η w = 0 := by
    have hn : w ∉ tsupport (fieldDerivative V η) := fun hz => hw (hsupport (S.tsupport_fieldDerivative_subset V η hz))
    rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have heB := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero
  have hd := fieldDerivative_puncturedKernel_mul_cutoff V hf hcθ heθ
  have hsub := fieldDerivative_one_sub_C1 V (hη.of_le (by simp))
  have hraw : fieldDerivative V (fun v => f v * (1 - η v)) =
      fun w => fieldDerivative V f w * (1 - η w) - f w * fieldDerivative V η w := by
    funext w
    rw [hd, hsub]
    change (1 - η w) * fieldDerivative V f w + f w * (-fieldDerivative V η w) = _
    ring
  rw [hraw]
  have hi := integral_sub hiA hiB.integrableOn
  change (∫ w in {w | ν w ≤ R}, fieldDerivative V f w * (1 - η w) - f w * fieldDerivative V η w) =
    (∫ w in {w | ν w ≤ R}, fieldDerivative V f w * (1 - η w)) -
    (∫ w in {w | ν w ≤ R}, f w * fieldDerivative V η w) at hi
  rw [hi, heB]

end RothschildStein.H1
