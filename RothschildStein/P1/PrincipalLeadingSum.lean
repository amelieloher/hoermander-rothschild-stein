-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalLeadingTypes
public import RothschildStein.P1.PrincipalModelDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- The actual finite sum of the two principal
contributions for each operator multi-index and field coordinate. -/
def PrincipalTerm.leadingKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w) (ξ η : Fin N → ℝ) : ℝ :=
  ∑ α ∈ t.indices.attach, ∑ j,
    ((t.leadingCoefficientDerivative α.val α.property j Y hY w hhY).kernel ξ η +
      (t.leadingPoleDerivative α.val α.property j Y hY w hhY).kernel ξ η)

/-- The constructed finite kernel has exactly
type λ-w; no decomposition or type assertion is assumed as an input. -/
theorem PrincipalTerm.leadingKernel_isTypeKernel (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w lam : ℕ) (hhY : G2.IsHomogeneousField F.G Y (w : ℤ))
    (hw : w ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F (lam - w) (t.leadingKernel Y hY (w : ℤ) hhY) := by
  classical
  apply IsTypeKernel.sum
  intro α _
  apply IsTypeKernel.sum
  intro j _
  exact (t.leadingCoefficientDerivative_isTypeKernel α.val α.property j Y hY w lam hhY hw hd).add
    (t.leadingPoleDerivative_isTypeKernel α.val α.property j Y hY w lam hhY hw hd)

/-- At each nonzero model coordinate, the
constructed kernel is precisely the cutoff model derivative Y(DΓ). -/
theorem PrincipalTerm.leadingKernel_eq (t : PrincipalTerm F)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w : ℤ) (hhY : G2.IsHomogeneousField F.G Y w)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (ξ η : Fin N → ℝ) (hu : F.Θ η ξ ≠ 0) :
    t.leadingKernel Y hY w hhY ξ η =
      t.a ξ * t.b η * fieldDerivative Y (t.modelKernel ξ η) (F.Θ η ξ) := by
  classical
  simp only [leadingKernel, leadingCoefficientDerivative_kernel, leadingPoleDerivative_kernel]
  rw [fieldDerivative_coordinate_sum]
  simp only [t.modelKernel_coordinate_derivative hΓ ξ η (F.Θ η ξ) hu]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  conv_rhs => rw [← Finset.sum_attach t.indices]
  apply Finset.sum_congr rfl
  intro α _
  ring

end RothschildStein.P1
