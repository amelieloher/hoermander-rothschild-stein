-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousPotentialTruncation
public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: the regularized potential differs from the
original locally integrable potential by exactly the omitted
weighted small-ball integral. -/
theorem regularizedPotential_sub_eq_neg_weightedSmallBall
    {ν f η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : LocallyIntegrable f volume) (hη : Continuous η)
    {R ε : ℝ} (hε : 0 < ε) (hηout : ∀ w, R ≤ ν w → η w = 0)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) (x : Fin N → ℝ) :
    G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w))) x -
      G2.groupConvolution G ψ f x =
      -(∫ w in {w | ν w ≤ R * ε}, f w * (η (G.dilate ε⁻¹ w) * ψ (G.mul x (G.inv w)))) := by
  have hηs : Continuous (fun w => η (G.dilate ε⁻¹ w)) := hη.comp (G2.continuous_dilate G ε⁻¹)
  have hθ : Continuous (fun w => 1 - η (G.dilate ε⁻¹ w)) := continuous_const.sub hηs
  have hreg : LocallyIntegrable (fun w => f w * (1 - η (G.dilate ε⁻¹ w))) volume := hf.mul_continuous hθ
  have hi := integrable_homogeneousPotential_integrand G hf hcψ hsψ x
  have hir := integrable_homogeneousPotential_integrand G hreg hcψ hsψ x
  have he : (fun w => (f w * (1 - η (G.dilate ε⁻¹ w))) * ψ (G.mul x (G.inv w)) - f w * ψ (G.mul x (G.inv w))) =
      fun w => -(f w * (η (G.dilate ε⁻¹ w) * ψ (G.mul x (G.inv w)))) := by
    funext w
    ring
  have hsub := integral_sub hir hi
  change (∫ w, (f w * (1 - η (G.dilate ε⁻¹ w))) * ψ (G.mul x (G.inv w)) - f w * ψ (G.mul x (G.inv w))) =
    (∫ w, (f w * (1 - η (G.dilate ε⁻¹ w))) * ψ (G.mul x (G.inv w))) - ∫ w, f w * ψ (G.mul x (G.inv w)) at hsub
  rw [he, integral_neg] at hsub
  have hsmall : (∫ w in {w | ν w ≤ R * ε}, f w * (η (G.dilate ε⁻¹ w) * ψ (G.mul x (G.inv w)))) =
      ∫ w, f w * (η (G.dilate ε⁻¹ w) * ψ (G.mul x (G.inv w))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    change ¬ν w ≤ R * ε at hw
    have hwν : R * ε ≤ ν w := (lt_of_not_ge hw).le
    have hz : η (G.dilate ε⁻¹ w) = 0 := by
      apply hηout
      rw [hν.2.2.2 ε⁻¹ (inv_pos.mpr hε), mul_comm ε⁻¹ (ν w), ← div_eq_mul_inv]
      exact (le_div_iff₀ hε).mpr hwν
    rw [hz, zero_mul, mul_zero]
  rw [G2.groupConvolution_def, G2.groupConvolution_def]
  have hc (g : (Fin N → ℝ) → ℝ) : (∫ w, ψ (G.mul x (G.inv w)) * g w) = ∫ w, g w * ψ (G.mul x (G.inv w)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  rw [hc, hc, hsmall]
  exact hsub.symm

end RothschildStein.H1
