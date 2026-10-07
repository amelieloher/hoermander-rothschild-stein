-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousKernelIntegrability
public import RothschildStein.H1.ConvolutionParameterSupport
public import RothschildStein.H1.PrincipalValueDefs
public import RothschildStein.G2.ConvolutionDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A locally integrable kernel gives an absolutely
convergent smooth-test potential at every point. -/
theorem integrable_homogeneousPotential_integrand
    {f ψ : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    (hc : Continuous ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    Integrable (fun w => f w * ψ (G.mul x (G.inv w))) volume := by
  have hg : Continuous (fun w => ψ (G.mul x (G.inv w))) :=
    hc.comp ((G2.continuous_mul G).comp (continuous_const.prodMk (G2.continuous_inv G)))
  simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport hg
    (hasCompactSupport_leftInv_translate G hs x)

/-- The truncation error for an integrable homogeneous
kernel is exactly its omitted small-ball potential. -/
theorem homogeneousPotential_truncation_sub_eq
    {f ψ ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : LocallyIntegrable f volume) (hc : Continuous ψ) (hs : HasCompactSupport ψ)
    (ε : ℝ) (x : Fin N → ℝ) :
    principalValueTruncation G ν f ψ ε x - G2.groupConvolution G ψ f x =
      -(∫ w in {w | ν w ≤ ε}, f w * ψ (G.mul x (G.inv w))) := by
  have hi := integrable_homogeneousPotential_integrand G hf hc hs x
  have hm : MeasurableSet {w | ν w ≤ ε} := (isClosed_le hν.1 continuous_const).measurableSet
  have hset : {w | ε < ν w} = {w | ν w ≤ ε}ᶜ := by ext w; simp
  have he := setIntegral_compl hm hi
  change (∫ w in {w | ν w ≤ ε}ᶜ, f w * ψ (G.mul x (G.inv w))) =
    (∫ w, f w * ψ (G.mul x (G.inv w))) - ∫ w in {w | ν w ≤ ε}, f w * ψ (G.mul x (G.inv w)) at he
  unfold principalValueTruncation
  rw [hset, he, G2.groupConvolution_def]
  have hall : (∫ w, ψ (G.mul x (G.inv w)) * f w) = ∫ w, f w * ψ (G.mul x (G.inv w)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  rw [hall]
  ring

end RothschildStein.H1
