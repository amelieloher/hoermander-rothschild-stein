-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ContinuousPuncturedCutoff
public import RothschildStein.H1.HomogeneousPotentialTruncation
public import RothschildStein.H1.DilatedCutoffTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 4: the actual smooth-cutoff potential splits
into the sharp truncation at Rε and its regularized small-ball term. -/
theorem regularizedPotential_eq_truncation_add_smallBall
    {ν F η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hη : Continuous η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R ε : ℝ} (hε : 0 < ε)
    (hηout : ∀ w, R ≤ ν w → η w = 0)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) (x : Fin N → ℝ) :
    G2.groupConvolution G ψ (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) x =
      principalValueTruncation G ν F ψ (R * ε) x +
        ∫ w in {w | ν w ≤ R * ε}, (F w * (1 - η (G.dilate ε⁻¹ w))) * ψ (G.mul x (G.inv w)) := by
  have hηs : Continuous (fun w => η (G.dilate ε⁻¹ w)) := hη.comp (G2.continuous_dilate G ε⁻¹)
  have he : (fun w => 1 - η (G.dilate ε⁻¹ w)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
    filter_upwards [cutoff_comp_dilate_eventually_one G heη ε⁻¹] with w hw
    change η (G.dilate ε⁻¹ w) = 1 at hw
    rw [hw, sub_self]
  have hθ : Continuous (fun w => 1 - η (G.dilate ε⁻¹ w)) := continuous_const.sub hηs
  have hreg : Continuous (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) :=
    continuous_puncturedKernel_mul_cutoff hF hθ he
  have hi : LocallyIntegrable (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) volume :=
    hreg.locallyIntegrable (μ := volume)
  have hcut (w : Fin N → ℝ) (hw : R * ε ≤ ν w) : η (G.dilate ε⁻¹ w) = 0 := by
    apply hηout
    rw [hν.2.2.2 ε⁻¹ (inv_pos.mpr hε), mul_comm ε⁻¹ (ν w), ← div_eq_mul_inv]
    exact (le_div_iff₀ hε).mpr hw
  have ht : principalValueTruncation G ν (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) ψ (R * ε) x =
      principalValueTruncation G ν F ψ (R * ε) x := by
    unfold principalValueTruncation
    apply setIntegral_congr_fun (isOpen_lt continuous_const hν.1).measurableSet
    intro w hw
    change (F w * (1 - η (G.dilate ε⁻¹ w))) * ψ (G.mul x (G.inv w)) =
      F w * ψ (G.mul x (G.inv w))
    rw [hcut w hw.le, sub_zero, mul_one]
  have heq := homogeneousPotential_truncation_sub_eq G hν hi hcψ hsψ (R * ε) x
  rw [ht] at heq
  linarith

end RothschildStein.H1
