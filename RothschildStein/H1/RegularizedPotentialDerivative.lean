-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.SmoothKernelPotentialDerivative
public import RothschildStein.H1.PuncturedKernelCutoff
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Step 1: the actual standing field derivative of a
regularized singular potential is the integral of the Leibniz kernel.
The original kernel needs only punctured C¹ regularity. -/
theorem StandingHypotheses.fieldDerivative_regularizedPotential
    (H : StandingHypotheses G q) (i : Fin (q + 1))
    {f θ ψ : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ 1 θ)
    (he : θ =ᶠ[nhds (0 : Fin N → ℝ)] fun _ => 0)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    fieldDerivative (H.fields i) (G2.groupConvolution G ψ (fun w => f w * θ w)) =
      G2.groupConvolution G ψ (fun w => θ w * fieldDerivative (H.fields i) f w +
        f w * fieldDerivative (H.fields i) θ w) := by
  have hreg := contDiff_puncturedKernel_mul_cutoff hf hθ he
  funext x
  rw [fieldDerivative_groupConvolution_C1 G (H.invariant i) hreg hc hs x,
    fieldDerivative_puncturedKernel_mul_cutoff (H.fields i) hf hθ he]

end RothschildStein.H1
