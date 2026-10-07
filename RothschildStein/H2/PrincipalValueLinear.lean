-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularHolder
public import RothschildStein.H2.HolderLinear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Additivity of the absolutely convergent regularized operator. -/
theorem LocalKernelData.regularized_add (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f g : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    (hg : BoundedHolder δ (ball Q.z Q.R) g) {x : X} (hx : x ∈ ball Q.z Q.R) :
    regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel (f + g) x =
      regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel f x +
        regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel g x := by
  have hi := Q.supported_localized_singular.regularized_absolute hδ hf hx
  have hj := Q.supported_localized_singular.regularized_absolute hδ hg hx
  unfold regularizedIntegral
  rw [← integral_add hi.1 hj.1]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp only [Pi.add_apply]; ring

/-- Homogeneity of the regularized operator. -/
theorem LocalKernelData.regularized_smul (Q : LocalKernelData D d) (c : ℝ)
    (f : X → ℝ) (x : X) :
    regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel (c • f) x =
      c * regularizedIntegral D.μ (ball Q.z Q.R) Q.cutoffKernel f x := by
  unfold regularizedIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Additivity of the principal value on the dense Hölder class. -/
theorem LocalKernelData.principalValue_add (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f g : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    (hg : BoundedHolder δ (ball Q.z Q.R) g) {x : X} (hx : x ∈ ball Q.z Q.R) :
    Q.principalValue (f + g) x = Q.principalValue f x + Q.principalValue g x := by
  unfold LocalKernelData.principalValue pvFormula
  rw [Q.regularized_add hδ hf hg hx]
  simp only [Pi.add_apply]
  ring

/-- Homogeneity of the principal value, with the fixed T(1) coefficient. -/
theorem LocalKernelData.principalValue_smul (Q : LocalKernelData D d) (c : ℝ)
    (f : X → ℝ) (x : X) : Q.principalValue (c • f) x = c * Q.principalValue f x := by
  unfold LocalKernelData.principalValue pvFormula
  rw [Q.regularized_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end RothschildStein.H2
