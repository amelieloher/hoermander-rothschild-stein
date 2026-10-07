-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixNoDriftPole
public import RothschildStein.P1.LeftParametrixKernel
public import RothschildStein.P1.RightParametrixNoDriftKernel

/-!
# The left parametrix error kernel without drift is jointly continuous off the diagonal

The no-drift counterpart of `LeftParametrixKernel`. For the reflected fundamental kernel `Γ*` of the
reversed no-drift model, an output cutoff `a` and `η, ξ ∈ C.U`, `ξ ≠ η`, the function
`Φ(ξ, η) = a(ξ) Γ*(Θ(η, ξ))` is jointly smooth on the off-diagonal set
(`LiftedChart.contDiffOn_kernelPhi_noDrift`). The no-drift formal adjoint `L̃*` (`sumSquaresTranspose`)
acting in the first variable (`adjoint1NoDrift`) keeps joint smoothness, and by the chain rule
(`𝓛Γ* = 0` off the origin)

`L̃*_ξ Φ(ξ, η) = a(ξ) (E_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) +
  (L̃* a)(ξ) Γ*(Θ(η, ξ))`

(`adjoint1_kernelPhi_eq_noDrift`): the bracket `leftErrBracketNoDrift` of the left error kernel is
jointly continuous on the off-diagonal set (`continuousOn_leftErrBracketNoDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

section Joint

variable {N : ℕ}

/-- The no-drift formal adjoint `L̃*` acting in the first variable
of a function of two variables. -/
def adjoint1NoDrift {q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  sumSquares1NoDrift X F p +
    2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i) p.1 * fd1 (X i) F p +
    adjointCoeffNoDrift X p.1 * F p

theorem contDiffOn_adjoint1NoDrift {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hS : IsOpen S)
    {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hdiv : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (Hormander.Interface.euclideanDivergence (X i)) U)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) (adjointCoeffNoDrift X) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (adjoint1NoDrift X F) S := by
  unfold adjoint1NoDrift
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => ∑ i : Fin q,
      Hormander.Interface.euclideanDivergence (X i) p.1 * fd1 (X i) F p) S :=
    ContDiffOn.sum fun i _ => ((hdiv i).comp contDiff_fst.contDiffOn (fun p hp => hSU p hp)).mul
      (contDiffOn_fd1 hS hSU (hX i) hF)
  exact ((contDiffOn_sumSquares1_noDrift hS hSU hX hF).add (contDiffOn_const.mul h2)).add
    ((hc.comp contDiff_fst.contDiffOn (fun p hp => hSU p hp)).mul hF)

/-- On the slice, `L̃*` of `ξ ↦ F(ξ, η)` is `L̃*` in the first variable of `F`
(no drift). -/
theorem sumSquaresTranspose_slice_fst_noDrift {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S)
    {ξ η : Fin N → ℝ} (hp : (ξ, η) ∈ S) :
    sumSquaresTranspose X (fun ξ' => F (ξ', η)) ξ = adjoint1NoDrift X F (ξ, η) := by
  have hslice : IsOpen {ξ' : Fin N → ℝ | (ξ', η) ∈ S} :=
    hS.preimage (continuous_id.prodMk continuous_const)
  let Ωs : Opens (Fin N → ℝ) := ⟨{ξ' : Fin N → ℝ | (ξ', η) ∈ S}, hslice⟩
  have hX' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ωs : Set (Fin N → ℝ)) := fun i =>
    (hX i).mono (fun x hx => hSU _ hx)
  have hF' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F (x, η)) (Ωs : Set (Fin N → ℝ)) :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => hx)
  rw [sumSquaresTranspose_apply Ωs X hX' _ hF' hp]
  have h1 : ∀ i : Fin q, fieldDerivative (X i) (fun x => F (x, η)) ξ =
      fd1 (X i) F (ξ, η) := fun i => fieldDerivative_slice_fst_of_contDiffOn hS hF hp
  have h2 : ∀ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i)
      (fun x => F (x, η))) ξ = fd1 (X i) (fd1 (X i) F) (ξ, η) := fun i =>
    fieldDerivative_fieldDerivative_slice_fst hS hSU (hX i) hF hp
  simp only [h1, h2]
  unfold adjoint1NoDrift sumSquares1NoDrift adjointCoeffNoDrift
  simp only [Finset.sum_mul]

end Joint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

theorem contDiffOn_adjointCoeff_XlNoDrift :
    ContDiffOn ℝ (⊤ : ℕ∞) (adjointCoeffNoDrift C.Xl) C.U := by
  have hdiv : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (Hormander.Interface.euclideanDivergence (C.Xl i)) C.U := fun i =>
    contDiffOn_euclideanDivergence C.chartOpens (C.Xl i) (C.contDiffOn_Xl_U i)
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (fun x =>
      fieldDerivative (C.Xl i) (Hormander.Interface.euclideanDivergence (C.Xl i)) x +
        Hormander.Interface.euclideanDivergence (C.Xl i) x ^ 2) C.U := fun i =>
    (S.contDiffOn_fieldDerivative C.chartOpens (C.Xl i) _ (C.contDiffOn_Xl_U i)
      (hdiv i)).add ((hdiv i).pow 2)
  exact ContDiffOn.sum fun i _ => h1 i

theorem contDiffOn_adjoint1_kernelPhi_noDrift {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (adjoint1NoDrift C.Xl (C.kernelPhiNoDrift K a))
      C.kernelOffDiagNoDrift :=
  contDiffOn_adjoint1NoDrift C.isOpen_kernelOffDiagNoDrift (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i)
    (fun i => contDiffOn_euclideanDivergence C.chartOpens (C.Xl i) (C.contDiffOn_Xl_U i))
    contDiffOn_adjointCoeff_XlNoDrift (contDiffOn_kernelPhi_noDrift hK ha)

/-- For `ξ ≠ η` the left error bracket is `L̃*_ξ` of the jointly smooth
`a(ξ) Γ*(Θ(η, ξ))` (by the chain rule and `𝓛Γ* = 0` off the origin):
`L̃*_ξ Φ(ξ, η) = a(ξ) (E_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) +
  (L̃* a)(ξ) Γ*(Θ(η, ξ))`. -/
theorem adjoint1_kernelPhi_eq_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ η : Fin (n + m) → ℝ}
    (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) :
    adjoint1NoDrift C.Xl (C.kernelPhiNoDrift K a) (ξ, η) = C.leftErrBracketNoDrift K a η ξ := by
  have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
  have hp : (ξ, η) ∈ C.kernelOffDiagNoDrift := ⟨hξ, hη, hne⟩
  rw [← sumSquaresTranspose_slice_fst_noDrift C.isOpen_kernelOffDiagNoDrift (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi_noDrift K.smooth_off_zero ha) hp]
  have h1 := C.sumSquaresTranspose_mul_comp_theta_noDrift hη isOpen_compl_singleton
    K.smooth_off_zero ha hξ hΘ
  have h2 : sumSquares C.Y (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) = 0 :=
    sumSquares_leftKernel_eq_zero_noDrift K hΘ
  change sumSquaresTranspose C.Xl (fun ξ' => a ξ' * K (C.Θ η ξ')) ξ = _
  rw [h1, h2, zero_add]
  rfl

/-- The left error bracket is jointly continuous on the off-diagonal set. -/
theorem continuousOn_leftErrBracketNoDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.leftErrBracketNoDrift K a p.2 p.1) C.kernelOffDiagNoDrift :=
  (contDiffOn_adjoint1_kernelPhi_noDrift K.smooth_off_zero ha).continuousOn.congr (fun _ hp =>
    (adjoint1_kernelPhi_eq_noDrift K ha hp.2.1 hp.1 hp.2.2).symm)

end LiftedChart

end RothschildStein.P1
