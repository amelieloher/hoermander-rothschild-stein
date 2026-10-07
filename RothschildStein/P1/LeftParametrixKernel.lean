-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixPole
public import RothschildStein.P1.RightParametrixMass

/-!
# The left parametrix error kernel is jointly continuous off the diagonal

For the reflected fundamental kernel `Γ*`, an output cutoff `a` and `η, ξ ∈ C.U`, `ξ ≠ η`, the
function `Φ(ξ, η) = a(ξ) Γ*(Θ(η, ξ))` is jointly smooth on the off-diagonal set
(`LiftedChart.contDiffOn_kernelPhi`). The formal adjoint `L̃*` (`sumSquaresWithDriftTranspose`) acting in the first
variable (`adjoint1`) keeps joint smoothness, and by the chain rule (`𝓛*Γ* = 0` off the origin)

`L̃*_ξ Φ(ξ, η) = a(ξ) (E*_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) +
  (L̃* a)(ξ) Γ*(Θ(η, ξ))`

(`adjoint1_kernelPhi_eq`): the bracket `leftErrBracket` of the left error kernel is jointly
continuous on the off-diagonal set (`continuousOn_leftErrBracket`).
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

/-- The formal adjoint `L̃*` acting in the first variable of a function
of two variables. -/
def adjoint1 {q : ℕ} (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  (∑ i : Fin q, fd1 (X i.succ) (fd1 (X i.succ) F) p - fd1 (X 0) F p) +
    2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i.succ) p.1 *
      fd1 (X i.succ) F p + adjointCoeff X p.1 * F p

theorem contDiffOn_adjoint1 {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hS : IsOpen S)
    {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hdiv : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (Hormander.Interface.euclideanDivergence (X i.succ)) U)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) (adjointCoeff X) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (adjoint1 X F) S := by
  unfold adjoint1
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => ∑ i : Fin q, fd1 (X i.succ) (fd1 (X i.succ) F) p) S :=
    ContDiffOn.sum fun i _ => contDiffOn_fd1 hS hSU (hX i.succ) (contDiffOn_fd1 hS hSU (hX i.succ) hF)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => ∑ i : Fin q,
      Hormander.Interface.euclideanDivergence (X i.succ) p.1 * fd1 (X i.succ) F p) S :=
    ContDiffOn.sum fun i _ => ((hdiv i).comp contDiff_fst.contDiffOn (fun p hp => hSU p hp)).mul
      (contDiffOn_fd1 hS hSU (hX i.succ) hF)
  exact ((h1.sub (contDiffOn_fd1 hS hSU (hX 0) hF)).add (contDiffOn_const.mul h2)).add
    ((hc.comp contDiff_fst.contDiffOn (fun p hp => hSU p hp)).mul hF)

theorem fieldDerivative_slice_fst_of_contDiffOn {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {V : (Fin N → ℝ) → (Fin N → ℝ)} {G : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) {ξ η : Fin N → ℝ} (hp : (ξ, η) ∈ S) :
    fieldDerivative V (fun x => G (x, η)) ξ = fd1 V G (ξ, η) :=
  fieldDerivative_slice_fst ((hG.contDiffAt (hS.mem_nhds hp)).differentiableAt (by simp))

theorem fieldDerivative_fieldDerivative_slice_fst {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) {ξ η : Fin N → ℝ}
    (hp : (ξ, η) ∈ S) :
    fieldDerivative V (fieldDerivative V (fun x => F (x, η))) ξ = fd1 V (fd1 V F) (ξ, η) := by
  have hslice : IsOpen {ξ' : Fin N → ℝ | (ξ', η) ∈ S} :=
    hS.preimage (continuous_id.prodMk continuous_const)
  have hev : fieldDerivative V (fun x => F (x, η)) =ᶠ[𝓝 ξ] fun x => fd1 V F (x, η) := by
    filter_upwards [hslice.mem_nhds hp] with x hx
    exact fieldDerivative_slice_fst_of_contDiffOn hS hF hx
  have h1 : fieldDerivative V (fieldDerivative V (fun x => F (x, η))) ξ =
      fieldDerivative V (fun x => fd1 V F (x, η)) ξ := by
    show fderiv ℝ (fieldDerivative V (fun x => F (x, η))) ξ (V ξ) =
      fderiv ℝ (fun x => fd1 V F (x, η)) ξ (V ξ)
    rw [hev.fderiv_eq]
  rw [h1]
  exact fieldDerivative_slice_fst_of_contDiffOn hS (contDiffOn_fd1 hS hSU hV hF) hp

/-- On the slice, `L̃*` of `ξ ↦ F(ξ, η)` is `L̃*` in the first variable of `F`. -/
theorem sumSquaresWithDriftTranspose_slice_fst {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S)
    {ξ η : Fin N → ℝ} (hp : (ξ, η) ∈ S) :
    sumSquaresWithDriftTranspose X (fun ξ' => F (ξ', η)) ξ = adjoint1 X F (ξ, η) := by
  have hslice : IsOpen {ξ' : Fin N → ℝ | (ξ', η) ∈ S} :=
    hS.preimage (continuous_id.prodMk continuous_const)
  let Ωs : Opens (Fin N → ℝ) := ⟨{ξ' : Fin N → ℝ | (ξ', η) ∈ S}, hslice⟩
  have hX' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ωs : Set (Fin N → ℝ)) := fun i =>
    (hX i).mono (fun x hx => hSU _ hx)
  have hF' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => F (x, η)) (Ωs : Set (Fin N → ℝ)) :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => hx)
  rw [sumSquaresWithDriftTranspose_apply Ωs X hX' _ hF' hp]
  have h1 : ∀ i : Fin (q + 1), fieldDerivative (X i) (fun x => F (x, η)) ξ =
      fd1 (X i) F (ξ, η) := fun i => fieldDerivative_slice_fst_of_contDiffOn hS hF hp
  have h2 : ∀ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ)
      (fun x => F (x, η))) ξ = fd1 (X i.succ) (fd1 (X i.succ) F) (ξ, η) := fun i =>
    fieldDerivative_fieldDerivative_slice_fst hS hSU (hX i.succ) hF hp
  simp only [h1, h2]
  unfold adjoint1 adjointCoeff
  simp only [sub_mul, Finset.sum_mul]
  ring

end Joint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

theorem contDiffOn_adjointCoeff_Xl : ContDiffOn ℝ (⊤ : ℕ∞) (adjointCoeff C.Xl) C.U := by
  have hdiv : ∀ i : Fin (q + 1), ContDiffOn ℝ (⊤ : ℕ∞)
      (Hormander.Interface.euclideanDivergence (C.Xl i)) C.U := fun i =>
    contDiffOn_euclideanDivergence C.chartOpens (C.Xl i) (C.contDiffOn_Xl_U i)
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (fun x =>
      fieldDerivative (C.Xl i.succ) (Hormander.Interface.euclideanDivergence (C.Xl i.succ)) x +
        Hormander.Interface.euclideanDivergence (C.Xl i.succ) x ^ 2) C.U := fun i =>
    (S.contDiffOn_fieldDerivative C.chartOpens (C.Xl i.succ) _ (C.contDiffOn_Xl_U i.succ)
      (hdiv i.succ)).add ((hdiv i.succ).pow 2)
  exact (ContDiffOn.sum fun i _ => h1 i).sub (hdiv 0)

theorem contDiffOn_adjoint1_kernelPhi {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (adjoint1 C.Xl (C.kernelPhi K a)) C.kernelOffDiag :=
  contDiffOn_adjoint1 C.isOpen_kernelOffDiag (fun _ hp => hp.1) (fun i => C.contDiffOn_Xl_U i)
    (fun i => contDiffOn_euclideanDivergence C.chartOpens (C.Xl i.succ)
      (C.contDiffOn_Xl_U i.succ)) contDiffOn_adjointCoeff_Xl (contDiffOn_kernelPhi hK ha)

/-- For `ξ ≠ η` the left error bracket is `L̃*_ξ` of the jointly smooth
`a(ξ) Γ*(Θ(η, ξ))` (by the chain rule and `𝓛*Γ* = 0` off the origin):
`L̃*_ξ Φ(ξ, η) = a(ξ) (E*_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) +
  (L̃* a)(ξ) Γ*(Θ(η, ξ))`. -/
theorem adjoint1_kernelPhi_eq {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G))
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ η : Fin (n + m) → ℝ}
    (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) :
    adjoint1 C.Xl (C.kernelPhi K a) (ξ, η) = C.leftErrBracket K a η ξ := by
  have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
  have hp : (ξ, η) ∈ C.kernelOffDiag := ⟨hξ, hη, hne⟩
  rw [← sumSquaresWithDriftTranspose_slice_fst C.isOpen_kernelOffDiag (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi K.smooth_off_zero ha) hp]
  have h1 := C.sumSquaresWithDriftTranspose_mul_comp_theta hη isOpen_compl_singleton
    K.smooth_off_zero ha hξ hΘ
  have h2 : C.modelAdjoint (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) = 0 := by
    rw [← sumSquaresWithDrift_reverseDrift_fields hq ν₀]
    exact sumSquaresWithDrift_kernel_eq_zero K hΘ
  change sumSquaresWithDriftTranspose C.Xl (fun ξ' => a ξ' * K (C.Θ η ξ')) ξ = _
  rw [h1, h2, zero_add]
  rfl

/-- The left error bracket is jointly continuous on the off-diagonal set. -/
theorem continuousOn_leftErrBracket {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G))
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.leftErrBracket K a p.2 p.1) C.kernelOffDiag :=
  (contDiffOn_adjoint1_kernelPhi K.smooth_off_zero ha).continuousOn.congr (fun _ hp =>
    (adjoint1_kernelPhi_eq K ha hp.2.1 hp.1 hp.2.2).symm)

end LiftedChart

end RothschildStein.P1
