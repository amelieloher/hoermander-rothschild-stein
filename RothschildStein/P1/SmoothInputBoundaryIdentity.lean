-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SmoothInputIntegrationByParts
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
namespace RothschildStein.P1
variable {N : ℕ}

/-- A locally C¹ input fiber has an exact boundary
identity, with genuine integrability of both terms before splitting. -/
theorem smoothInput_boundary_integral_eq (V : Opens (Fin N → ℝ))
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (V : Set (Fin N → ℝ)))
    (g χ : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ 1 g (V : Set (Fin N → ℝ)))
    (hχ : ContDiffOn ℝ 1 χ (V : Set (Fin N → ℝ)))
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    (∫ η, -(fieldDerivative Y χ η) * g η * φ η) =
      (∫ η, (χ η * g η) * fieldDerivative Y φ η) -
      ∫ η, χ η * (-fieldDerivative Y g η -
        g η * Hormander.Interface.euclideanDivergence Y η) * φ η := by
  have hcDg : ContinuousOn (fieldDerivative Y g) (V : Set (Fin N → ℝ)) :=
    (hg.continuousOn_fderiv_of_isOpen V.isOpen (by rfl)).clm_apply hY.continuousOn
  have hcDχ : ContinuousOn (fieldDerivative Y χ) (V : Set (Fin N → ℝ)) :=
    (hχ.continuousOn_fderiv_of_isOpen V.isOpen (by rfl)).clm_apply hY.continuousOn
  have hcadj := hcDg.neg.sub (hg.continuousOn.mul
    (contDiffOn_euclideanDivergence V Y hY).continuousOn)
  have hia := S.integrable_mul_test V
    ((hχ.continuousOn.mul hcadj).locallyIntegrableOn (μ := volume) V.isOpen.measurableSet) φ
  have hib := S.integrable_mul_test V
    ((hcDχ.neg.mul hg.continuousOn).locallyIntegrableOn (μ := volume) V.isOpen.measurableSet) φ
  have hi := smoothInput_integral_integrationByParts V Y hY (fun η => χ η * g η) (hχ.mul hg) φ
  have he : (fun η => (-fieldDerivative Y (fun η => χ η * g η) η -
      (χ η * g η) * Hormander.Interface.euclideanDivergence Y η) * φ η) =ᵐ[volume]
      fun η => (χ η * (-fieldDerivative Y g η -
        g η * Hormander.Interface.euclideanDivergence Y η) * φ η) +
        (-(fieldDerivative Y χ η) * g η * φ η) := by
    apply Eventually.of_forall
    intro η
    by_cases hη : η ∈ (V : Set (Fin N → ℝ))
    · have hdχ := (hχ.contDiffAt (V.isOpen.mem_nhds hη)).differentiableAt (by simp)
      have hdg := (hg.contDiffAt (V.isOpen.mem_nhds hη)).differentiableAt (by simp)
      change (-fieldDerivative Y (fun η => χ η * g η) η - _) * φ η = _
      rw [S.fieldDerivative_mul Y χ g η hdχ hdg]
      ring
    · simp only [φ.zero_on_compl hη, Pi.zero_apply, mul_zero, add_zero]
  rw [integral_congr_ae he, integral_add
    (f := fun η => χ η * (-fieldDerivative Y g η -
      g η * Hormander.Interface.euclideanDivergence Y η) * φ η)
    (g := fun η => -(fieldDerivative Y χ η) * g η * φ η) hia hib] at hi
  linarith

end RothschildStein.P1
