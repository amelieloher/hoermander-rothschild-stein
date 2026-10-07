-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularTransferErrorKernel
public import RothschildStein.P1.RegularKernelWeakWordDerivative
public import RothschildStein.P1.SmoothInputIntegrationByParts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace RothschildStein.P1

/-- Every regular kernel row times an interior
test is integrable, including at the least regularity budget (BB p. 556). -/
theorem IsRegularKernel.transfer_row_integrable {N b : ℕ} {F : KernelFrame N}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F b r)
    (ξ : Fin N → ℝ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => r ξ η * φ η) := by
  have hc : Continuous (fun η => r ξ η * φ η) :=
    (hr.1.continuous.comp (continuous_const.prodMk continuous_id)).mul φ.contDiff.continuous
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left

namespace LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- For a regular kernel, transfer gives the
actual weak output derivative directly by classical input integration
by parts. Coefficient derivatives and divergences remain in the error
(BB Theorem 11.24, pp. 555–558). -/
theorem regularTransfer_action_hasWeakWordDeriv (hF : C.IsLiftedFrame F)
    {r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ} (hr : IsRegularKernel F 1 r)
    (i : Fin k) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv C.Xl F.V [i] (fun ξ => ∫ η, r ξ η * φ η)
      (fun ξ => (∑ j, ∫ η, C.generatorTransferKernel F i j r ξ η *
        fieldDerivative (wordBracket C.Xl (C.B j)) φ η) +
        ∫ η, C.regularTransferErrorKernel F i r ξ η * φ η) := by
  classical
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  have hp (j : Fin (n+m)) : IsRegularKernel F 1 (C.generatorTransferKernel F i j r) :=
    C.isRegularKernel_modelMultiplier F hF.Θ_eq hVU hr
      (fun u => MvPolynomial.eval u (C.generatorTransferCoefficient i j)) (G2.contDiff_eval _)
  let D := fun j ξ η => fieldDerivative (wordBracket C.Xl (C.B j))
    (fun ζ => C.generatorTransferKernel F i j r ξ ζ) η
  let E := fun j ξ η => C.generatorTransferKernel F i j r ξ η *
    Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η
  have hD (j : Fin (n+m)) : IsRegularKernel F 0 (D j) :=
    (hp j).fieldDerivative_input _ (C.transferBasis_smooth F hF j)
  have hE (j : Fin (n+m)) : IsRegularKernel F 0 (E j) := by
    have h := (hp j).inputMultiplier (Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)))
      (contDiffOn_euclideanDivergence F.V _ (C.transferBasis_smooth F hF j))
    exact ⟨h.1.of_le (by simp), h.2⟩
  have hX : IsRegularKernel F 0 (fun ξ η => fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ) :=
    hr.fieldDerivative_output _ (C.transferGenerator_smooth F hF i)
  have heq : (fun ξ => ∫ η, fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ * φ η) =
      fun ξ => (∑ j, ∫ η, C.generatorTransferKernel F i j r ξ η *
        fieldDerivative (wordBracket C.Xl (C.B j)) φ η) +
        ∫ η, C.regularTransferErrorKernel F i r ξ η * φ η := by
    funext ξ
    have hiD := fun j => (hD j).transfer_row_integrable ξ φ
    have hiE := fun j => (hE j).transfer_row_integrable ξ φ
    have hiX := hX.transfer_row_integrable ξ φ
    have hibp (j : Fin (n+m)) :
        (∫ η, C.generatorTransferKernel F i j r ξ η *
          fieldDerivative (wordBracket C.Xl (C.B j)) φ η) =
        -(∫ η, D j ξ η * φ η) - ∫ η, E j ξ η * φ η := by
      have hs : ContDiffOn ℝ 1 (C.generatorTransferKernel F i j r ξ) (F.V : Set (Fin (n+m) → ℝ)) :=
        ((hp j).1.comp (contDiff_const.prodMk contDiff_id)).contDiffOn
      rw [smoothInput_integral_integrationByParts F.V _ (C.transferBasis_smooth F hF j) _ hs φ]
      have ht : (fun η => (-fieldDerivative (wordBracket C.Xl (C.B j))
          (C.generatorTransferKernel F i j r ξ) η -
          C.generatorTransferKernel F i j r ξ η *
            Hormander.Interface.euclideanDivergence (wordBracket C.Xl (C.B j)) η) * φ η) =
          fun η => -(D j ξ η * φ η) - E j ξ η * φ η := by
        funext η; dsimp only [D, E]; ring
      rw [ht, integral_sub (f := fun η => -(D j ξ η * φ η)) (hiD j).neg (hiE j), integral_neg]
    have hf : (fun η => C.regularTransferErrorKernel F i r ξ η * φ η) =
        fun η => fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ * φ η +
          (∑ j, D j ξ η * φ η) + ∑ j, E j ξ η * φ η := by
      funext η
      simp only [regularTransferErrorKernel, D, E, add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _; ring
    have hiSD : Integrable (fun η => ∑ j, D j ξ η * φ η) :=
      integrable_finsetSum Finset.univ (fun j _ => hiD j)
    have hiSE : Integrable (fun η => ∑ j, E j ξ η * φ η) :=
      integrable_finsetSum Finset.univ (fun j _ => hiE j)
    rw [hf, integral_add
      (f := fun η => fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ * φ η + ∑ j, D j ξ η * φ η)
      (g := fun η => ∑ j, E j ξ η * φ η) (hiX.add hiSD) hiSE,
      integral_add (f := fun η => fieldDerivative (C.Xl i) (fun ζ => r ζ η) ξ * φ η)
        (g := fun η => ∑ j, D j ξ η * φ η) hiX hiSD,
      integral_finsetSum Finset.univ (fun j _ => hiD j),
      integral_finsetSum Finset.univ (fun j _ => hiE j)]
    simp_rw [hibp]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  have hw := regularKernel_action_hasWeakWordDeriv hr C.Xl i
    (C.transferGenerator_smooth F hF i) φ
  rw [heq] at hw
  exact hw

end LiftedChart
end RothschildStein.P1
