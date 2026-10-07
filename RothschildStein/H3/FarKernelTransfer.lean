-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InversionFields
public import RothschildStein.G2.InvariantIntegration
public import RothschildStein.G2.ConvolutionSubstitution
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3
open G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- far part. A compact continuous input and a globally
continuous exterior kernel give absolute convergence at every point. -/
theorem groupConvolution_exists_compact_continuous_kernel
    {u F : (Fin N → ℝ) → ℝ} (hu : Continuous u) (hsu : HasCompactSupport u)
    (hF : Continuous F) (x : Fin N → ℝ) : GroupConvolutionExistsAt G u F x := by
  have hm : Continuous (fun y : Fin N → ℝ => G.mul (G.inv y) x) :=
    (contDiff_rightTranslation G x).continuous.comp (continuous_inv G)
  have hk : Continuous (fun y : Fin N → ℝ => F (G.mul (G.inv y) x)) := hF.comp hm
  change Integrable (fun y => u y * F (G.mul (G.inv y) x)) volume
  exact (hu.mul hk).integrable_of_hasCompactSupport hsu.mul_right

/-- far part. Differentiating the actual inverse-translation
kernel in its input variable gives minus the matching right field.
BB Proposition 3.47(c), used on p. 383. -/
theorem leftField_inverse_kernel (v x : Fin N → ℝ)
    {F : (Fin N → ℝ) → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y : Fin N → ℝ) :
    fieldDerivative (leftField G v) (fun z => F (G.mul (G.inv z) x)) y =
      -fieldDerivative (rightField G v) F (G.mul (G.inv y) x) := by
  let f := F ∘ (fun z => G.mul z x)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hF.comp (contDiff_rightTranslation G x)
  have hi := rightField_action_inv G v f (hf.differentiable (by simp)) (G.inv y)
  rw [inv_inv G y] at hi
  have hr := congrFun ((rightField_invariant G v).operator G F hF x) (G.inv y)
  change fieldDerivative (rightField G v) f (G.inv y) =
    fieldDerivative (rightField G v) F (G.mul (G.inv y) x) at hr
  rw [hr] at hi
  change fieldDerivative (rightField G v) F (G.mul (G.inv y) x) =
    -fieldDerivative (leftField G v) (fun z => F (G.mul (G.inv z) x)) y at hi
  linarith

/-- far part. One derivative transfers from a smooth compact
input to the smooth far kernel, with absolute convergence inherited
from compact support. No boundedness of the kernel is required here. -/
theorem groupConvolution_leftField_transfer (v : Fin N → ℝ)
    {u F : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hsu : HasCompactSupport u) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Fin N → ℝ) :
    groupConvolution G (fieldDerivative (leftField G v) u) F x =
      groupConvolution G u (fieldDerivative (rightField G v) F) x := by
  have hK : ContDiff ℝ (⊤ : ℕ∞) (fun y => F (G.mul (G.inv y) x)) :=
    hF.comp ((contDiff_rightTranslation G x).comp (contDiff_inv G))
  have hi := integral_leftField_mul G v (fun y => F (G.mul (G.inv y) x)) u hK hu hsu
  have he : fieldDerivative (leftField G v) (fun y => F (G.mul (G.inv y) x)) =
      fun y => -fieldDerivative (rightField G v) F (G.mul (G.inv y) x) :=
    funext (leftField_inverse_kernel G v x hF)
  rw [he] at hi
  simp only [neg_mul, integral_neg] at hi
  rw [groupConvolution_eq_integral, groupConvolution_eq_integral]
  have hc : (∫ y, F (G.mul (G.inv y) x) * fieldDerivative (leftField G v) u y) =
      ∫ y, fieldDerivative (leftField G v) u y * F (G.mul (G.inv y) x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  have hd : (∫ y, fieldDerivative (rightField G v) F (G.mul (G.inv y) x) * u y) =
      ∫ y, u y * fieldDerivative (rightField G v) F (G.mul (G.inv y) x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  rw [hc, hd] at hi
  linarith

/-- far part. Both derivatives of a horizontal square
transfer to the actual right-invariant kernel, with the source order. -/
theorem groupConvolution_leftField_square_transfer (v : Fin N → ℝ)
    {u F : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hsu : HasCompactSupport u) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Fin N → ℝ) :
    groupConvolution G (fieldDerivative (leftField G v)
      (fieldDerivative (leftField G v) u)) F x =
    groupConvolution G u (fieldDerivative (rightField G v)
      (fieldDerivative (rightField G v) F)) x := by
  have hdu : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (leftField G v) u) :=
    contDiffOn_univ.mp (S.contDiffOn_fieldDerivative ⊤ _ u
      (contDiff_leftField G v).contDiffOn hu.contDiffOn)
  have hsdu : HasCompactSupport (fieldDerivative (leftField G v) u) :=
    hsu.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset _ _)
  have hdF : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (rightField G v) F) :=
    contDiffOn_univ.mp (S.contDiffOn_fieldDerivative ⊤ _ F
      (contDiff_rightField G v).contDiffOn hF.contDiffOn)
  rw [groupConvolution_leftField_transfer G v hdu hsdu hF x,
    groupConvolution_leftField_transfer G v hu hsu hdF x]

end RothschildStein.H3
