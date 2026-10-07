-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.AdjointExpansion
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace RothschildStein.P1
variable {N : ℕ}

/-- Input integration by parts for a smooth
fiber has the complete formal-adjoint expression, including divergence.
Only local regularity on the test domain is required. -/
theorem smoothInput_integral_integrationByParts (V : Opens (Fin N → ℝ))
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (V : Set (Fin N → ℝ)))
    (g : (Fin N → ℝ) → ℝ) (hg : ContDiffOn ℝ 1 g (V : Set (Fin N → ℝ)))
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    (∫ η, g η * fieldDerivative Y φ η) =
      ∫ η, (-fieldDerivative Y g η - g η * Hormander.Interface.euclideanDivergence Y η) * φ η := by
  have hgc := hg.continuousOn.locallyIntegrableOn (μ := volume) V.isOpen.measurableSet
  have hdg : ContinuousOn (fieldDerivative Y g) (V : Set (Fin N → ℝ)) :=
    (hg.continuousOn_fderiv_of_isOpen V.isOpen (by rfl)).clm_apply hY.continuousOn
  have hiD : IntegrableOn (fun η => fieldDerivative Y g η * φ η)
      (V : Set (Fin N → ℝ)) volume :=
    (S.integrable_mul_test V
      (hdg.locallyIntegrableOn (μ := volume) V.isOpen.measurableSet) φ).integrableOn
  have hdiv : ContinuousOn (fun η => g η * Hormander.Interface.euclideanDivergence Y η)
      (V : Set (Fin N → ℝ)) :=
    hg.continuousOn.mul (contDiffOn_euclideanDivergence V Y hY).continuousOn
  have hiDiv : IntegrableOn (fun η => (g η * Hormander.Interface.euclideanDivergence Y η) * φ η)
      (V : Set (Fin N → ℝ)) volume :=
    (S.integrable_mul_test V
      (hdiv.locallyIntegrableOn (μ := volume) V.isOpen.measurableSet) φ).integrableOn
  let dφ := S.wordDerivativeTest V (fun _ : Fin 1 => Y) (fun _ => hY) [0] φ
  have heφ : (dφ : (Fin N → ℝ) → ℝ) = fieldDerivative Y φ := rfl
  have hiφ : IntegrableOn (fun η => g η * fieldDerivative Y φ η)
      (V : Set (Fin N → ℝ)) volume := by
    simpa only [heφ] using (S.integrable_mul_test V hgc dφ).integrableOn
  have hibp := S.integral_fieldDerivative_mul_test V Y hY g hg φ
  have heT : (fun η => g η * fieldTranspose Y φ η) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      fun η => -(g η * fieldDerivative Y φ η) -
        (g η * Hormander.Interface.euclideanDivergence Y η) * φ η := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with η hη
    rw [S.fieldTranspose_formula Y φ η
      ((hY.contDiffAt (V.isOpen.mem_nhds hη)).differentiableAt (by simp))
      ((φ.contDiff.differentiable (by simp)).differentiableAt)]
    ring
  rw [integral_congr_ae heT,
    integral_sub (f := fun η => -(g η * fieldDerivative Y φ η)) hiφ.neg hiDiv,
    integral_neg] at hibp
  have heR : (fun η => (-fieldDerivative Y g η - g η *
      Hormander.Interface.euclideanDivergence Y η) * φ η) =
      fun η => -(fieldDerivative Y g η * φ η) -
        (g η * Hormander.Interface.euclideanDivergence Y η) * φ η := by
    funext η
    ring
  have heL : (∫ η in (V : Set (Fin N → ℝ)), g η * fieldDerivative Y φ η) =
      ∫ η, g η * fieldDerivative Y φ η :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      have hz : fieldDerivative Y φ η = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hη
          (φ.tsupport_subset (S.tsupport_fieldDerivative_subset Y φ ht)))
      rw [hz, mul_zero])
  have heOut : (∫ η in (V : Set (Fin N → ℝ)),
      (-fieldDerivative Y g η - g η * Hormander.Interface.euclideanDivergence Y η) * φ η) =
      ∫ η, (-fieldDerivative Y g η - g η * Hormander.Interface.euclideanDivergence Y η) * φ η :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      simp only [φ.zero_on_compl hη, Pi.zero_apply, mul_zero])
  rw [← heL, ← heOut, heR,
    integral_sub (f := fun η => -(fieldDerivative Y g η * φ η)) hiD.neg hiDiv,
    integral_neg]
  linarith

end RothschildStein.P1
