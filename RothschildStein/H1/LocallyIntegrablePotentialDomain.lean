-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousPotentialTruncation
public import RothschildStein.G2.ConvolutionSupport
public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Locally integrable kernels and compact continuous tests
satisfy the actual first-formula absolute-convergence predicate. -/
theorem groupConvolutionExistsAt_of_localKernel
    {f ψ : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    G2.GroupConvolutionExistsAt G ψ f x := by
  have hi := integrable_homogeneousPotential_integrand G hf hc hs x
  let F := fun y => ψ y * f (G.mul (G.inv y) x)
  have hp := G2.measurePreserving_leftInvAt G x
  have he : MeasurableEmbedding (fun w : Fin N → ℝ => G.mul x (G.inv w)) :=
    hp.measurable.measurableEmbedding
      ((G2.leftTranslation_bijective G x).comp (G2.inv_bijective G)).injective
  have hcF : Integrable (F ∘ (fun w => G.mul x (G.inv w))) volume := by
    convert hi using 1
    funext w
    change ψ (G.mul x (G.inv w)) * f (G.mul (G.inv (G.mul x (G.inv w))) x) =
      f w * ψ (G.mul x (G.inv w))
    rw [G2.inv_product, G2.inv_inv, G2.mul_assoc, G2.inv_mul, G2.mul_zero]
    ring
  exact (hp.integrable_comp_emb he).mp hcF

/-- The existing group-convolution additivity theorem
applies to every pair of locally integrable kernels. -/
theorem groupConvolution_add_localKernels
    {f g ψ : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (hc : Continuous ψ) (hs : HasCompactSupport ψ) :
    G2.groupConvolution G ψ (f + g) = G2.groupConvolution G ψ f + G2.groupConvolution G ψ g := by
  funext x
  exact G2.groupConvolution_add_right G ψ f g x
    (groupConvolutionExistsAt_of_localKernel G hf hc hs x)
    (groupConvolutionExistsAt_of_localKernel G hg hc hs x)

end RothschildStein.H1
