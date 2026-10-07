-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Representation
public import RothschildStein.G2.ConvolutionSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The noncommutative potential is globally smooth by differentiation
under the parameter integral, rather than abelian convolution
(BB Theorem 6.20(3), printed pp. 269–270). -/
theorem contDiff_fundamentalPotential {Γ φ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, Γ (G.mul (G.inv y) x) * φ y) := by
  have he : (fun x => ∫ y, Γ (G.mul (G.inv y) x) * φ y) =
      G2.groupConvolution G φ Γ := by
    funext x
    rw [G2.groupConvolution_eq_integral]
    simp only [mul_comm]
  rw [he]
  exact G2.contDiff_groupConvolution_left G hφ hc hΓ

/-- Absolute convergence of the potential integral when Gamma is
locally integrable (BB printed p. 270). -/
theorem integrable_fundamentalPotential_first {Γ φ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (x : Fin N → ℝ) :
    Integrable (fun w => Γ w * φ (G.mul x (G.inv w))) := by
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := fun w => G.mul x (G.inv w)
      invFun := fun y => G.mul (G.inv y) x
      left_inv := by intro w; simp only [G2.inv_product, G2.inv_inv,
        G2.mul_assoc, G2.inv_mul, G2.mul_zero]
      right_inv := by intro y; simp only [G2.inv_product, G2.inv_inv,
        ← G2.mul_assoc, G2.mul_inv, G2.zero_mul]
      continuous_toFun := ((G2.contDiff_leftTranslation G x).continuous).comp (G2.continuous_inv G)
      continuous_invFun := ((G2.contDiff_rightTranslation G x).continuous).comp (G2.continuous_inv G) }
  exact hΓ.integrable_smul_right_of_hasCompactSupport (hφ.comp e.continuous)
    (hc.comp_homeomorph e)

/-- Absolute convergence in the original integration variable
(BB printed p. 270). -/
theorem integrable_fundamentalPotential_second {Γ φ : (Fin N → ℝ) → ℝ}
    (hΓ : LocallyIntegrable Γ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (x : Fin N → ℝ) :
    Integrable (fun y => Γ (G.mul (G.inv y) x) * φ y) := by
  have hi := (G2.measurePreserving_invRightAt G x).integrable_comp_of_integrable
    (integrable_fundamentalPotential_first G hΓ hφ hc x)
  simpa only [Function.comp_def, G2.inv_product, G2.inv_inv, ← G2.mul_assoc, G2.mul_inv,
    G2.zero_mul] using hi

end RothschildStein.H1
