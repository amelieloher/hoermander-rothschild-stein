-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferKernels
public import RothschildStein.P1.TransferRemainderLeadingType
public import RothschildStein.P1.TransferIbpCoefficient
public import RothschildStein.P1.LocalSmoothPrincipalMultiplier
public import RothschildStein.P1.PrincipalInputCutoffDerivative
public import RothschildStein.P1.PrincipalInputEndpointKernel
public import RothschildStein.P1.PrincipalCutoffDerivative
public import RothschildStein.P1.PrincipalEndpointKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- Lifted generators are smooth on the
frame's test domain (BB Theorem 11.24). -/
theorem transferGenerator_smooth (hF : C.IsLiftedFrame F) (i : Fin k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n+m) → ℝ)) :=
  (C.lift_smooth i).mono ((subset_closure.trans hF.closure_subset).trans C.U_subset_O)

/-- The actual input basis bracket is smooth
on the frame's test domain (BB Theorem 11.24). -/
theorem transferBasis_smooth (hF : C.IsLiftedFrame F) (j : Fin (n+m)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordBracket C.Xl (C.B j)) (F.V : Set (Fin (n+m) → ℝ)) :=
  G1.wordBracket_contDiffOn F.V.isOpen C.Xl (fun i => C.transferGenerator_smooth F hF i) (C.B j)

/-- The constructed error kernel retains both
endpoint parameter derivatives, both cutoff derivatives, the complete
coefficient/divergence correction, and the full transfer remainder
(BB (11.36)–(11.37), pp. 555–556). -/
def principalTransferErrorKernel (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    (i : Fin k) (ξ η : Fin (n+m) → ℝ) : ℝ :=
  (t.cutoffDerivative (C.Xl i) (C.transferGenerator_smooth F hF i)).kernel ξ η +
  t.endpointKernel (C.Xl i) (C.transferGenerator_smooth F hF i) ξ η +
  (∑ j, C.generatorTransferKernel F i j
    (fun x y => (t.inputCutoffDerivative (wordBracket C.Xl (C.B j))
        (C.transferBasis_smooth F hF j)).kernel x y +
      t.inputEndpointKernel (wordBracket C.Xl (C.B j))
        (C.transferBasis_smooth F hF j) x y) ξ η) +
  (∑ j, C.transferIbpCoefficient i j (ξ, η) * t.kernel ξ η) +
  ∑ l, C.generatorTransferRemainder i ξ η (F.Θ η ξ) l *
    t.leadingKernel (fun _ => Pi.single l 1) contDiff_const (F.G.weight l : ℤ)
      (coordinateField_homogeneous F.G l) ξ η

/-- Every term of the constructed error has
at least type λ+1-w_i; the only term needing weighted Taylor jets is
the full transfer remainder (BB Theorem 11.24, pp. 555–558). -/
theorem isTypeKernel_principalTransferErrorKernel (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (i : Fin k) (lam : ℕ) (hw : (w i : ℕ) ≤ lam)
    (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F (lam + 1 - (w i : ℕ)) (C.principalTransferErrorKernel F hF t i) := by
  classical
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  have hwi : 1 ≤ (w i : ℕ) := (w i).2
  have hl : lam + 1 - (w i : ℕ) ≤ lam := by omega
  unfold principalTransferErrorKernel
  apply IsTypeKernel.add
  · apply IsTypeKernel.add
    · apply IsTypeKernel.add
      · apply IsTypeKernel.add
        · exact (t.cutoffDerivative_isTypeKernel (C.Xl i) (C.transferGenerator_smooth F hF i) lam hd).mono hl
        · exact (t.endpointKernel_isTypeKernel (C.Xl i) (C.transferGenerator_smooth F hF i) lam hd).mono hl
      · apply IsTypeKernel.sum
        intro j _
        have hb : 1 ≤ wordWeight w (C.B j) := by
          have hne := (C.basis_weight j).1
          cases hBj : C.B j with
          | nil => exact False.elim (hne hBj)
          | cons l I => simp only [wordWeight, List.map_cons, List.sum_cons]; exact (Nat.succ_le_of_lt (w l).2).trans (Nat.le_add_right _ _)
        exact (C.isTypeKernel_generatorTransferKernel F hF
          ((t.inputCutoffDerivative_isTypeKernel (wordBracket C.Xl (C.B j))
            (C.transferBasis_smooth F hF j) lam hd).add
          (t.inputEndpointKernel_isTypeKernel (wordBracket C.Xl (C.B j))
            (C.transferBasis_smooth F hF j) lam hd)) i j).mono (by omega)
    · apply IsTypeKernel.sum
      intro j _
      exact (C.isTypeKernel_local_smooth_principal_multiplier F hF.Θ_eq hVU t lam hd
        (hF.pole_smooth t.star)
        (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star)
        (C.transferIbpCoefficient i j) (C.transferIbpCoefficient_smooth i j)).mono hl
  · apply IsTypeKernel.sum
    intro l _
    exact C.isTypeKernel_transfer_remainder_times_leadingKernel F hF.Θ_eq hF.G_eq hVU
      t i l lam hw hd (hF.pole_smooth t.star)
      (by simpa only [hF.G_eq] using hF.pole_homogeneous t.star)

end RothschildStein.P1.LiftedChart
