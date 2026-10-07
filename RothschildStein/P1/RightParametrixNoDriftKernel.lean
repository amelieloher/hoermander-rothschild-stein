-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixKernel
public import RothschildStein.P1.RightParametrixNoDriftError

/-!
# The right parametrix kernel without drift and its error kernel are jointly smooth off the
diagonal

The no-drift counterpart of `RightParametrixKernel`. For the H1 fundamental kernel `Γ` of the
no-drift model, an output cutoff `a` and `η, ξ ∈ C.U`, `ξ ≠ η`, the function
`Φ(ξ, η) = a(ξ) Γ(Θ(η, ξ))` is jointly smooth on `S₀ = {(ξ, η) ∈ C.U × C.U | ξ ≠ η}`. Applying
`L̃ = ∑ᵢ X̃ᵢ²` in the first variable (`sumSquares1NoDrift`) keeps joint smoothness, and by the right pole formula
with `𝓛Γ = 0` off the origin

`L̃_ξ Φ(ξ, η) = a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`

(`sumSquares1_kernelPhi_eq_noDrift`): the bracket of the error kernel of the right pole computation is
jointly continuous on `S₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1

section Joint

variable {N : ℕ}

/-- `L̃ = ∑ Xᵢ²` acting in the first variable of a function of two variables. -/
def sumSquares1NoDrift {q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  ∑ i : Fin q, fd1 (X i) (fd1 (X i) F) p

theorem contDiffOn_sumSquares1_noDrift {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquares1NoDrift X F) S :=
  ContDiffOn.sum fun i _ =>
    contDiffOn_fd1 hS hSU (hX i) (contDiffOn_fd1 hS hSU (hX i) hF)

/-- On the slice, `L̃` of `ξ ↦ F(ξ, η)` is `L̃` in the first variable of `F`. -/
theorem sumSquares_slice_fst_noDrift {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S)
    {ξ η : Fin N → ℝ} (hp : (ξ, η) ∈ S) :
    sumSquares X (fun ξ' => F (ξ', η)) ξ = sumSquares1NoDrift X F (ξ, η) := by
  have hd : ∀ {G : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) G S →
      ∀ {z : (Fin N → ℝ) × (Fin N → ℝ)}, z ∈ S → DifferentiableAt ℝ G z := fun hG z hz =>
    (hG.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
  have hslice : IsOpen {ξ' : Fin N → ℝ | (ξ', η) ∈ S} :=
    hS.preimage (continuous_id.prodMk continuous_const)
  have key : ∀ (V : (Fin N → ℝ) → (Fin N → ℝ)) (G : (Fin N → ℝ) × (Fin N → ℝ) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) G S → ∀ ξ' : Fin N → ℝ, (ξ', η) ∈ S →
        fieldDerivative V (fun x => G (x, η)) ξ' = fd1 V G (ξ', η) :=
    fun V G hG ξ' h' => fieldDerivative_slice_fst (hd hG h')
  have hev : ∀ (V : (Fin N → ℝ) → (Fin N → ℝ)) (G : (Fin N → ℝ) × (Fin N → ℝ) → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) G S →
        fieldDerivative V (fun x => G (x, η)) =ᶠ[𝓝 ξ] fun x => fd1 V G (x, η) := by
    intro V G hG
    filter_upwards [hslice.mem_nhds hp] with x hx
    exact key V G hG x hx
  have second : ∀ V : (Fin N → ℝ) → (Fin N → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) V U →
      fieldDerivative V (fieldDerivative V (fun x => F (x, η))) ξ = fd1 V (fd1 V F) (ξ, η) := by
    intro V hV
    have h1 : fieldDerivative V (fieldDerivative V (fun x => F (x, η))) ξ =
        fieldDerivative V (fun x => fd1 V F (x, η)) ξ := by
      show fderiv ℝ (fieldDerivative V (fun x => F (x, η))) ξ (V ξ) =
        fderiv ℝ (fun x => fd1 V F (x, η)) ξ (V ξ)
      rw [(hev V F hF).fderiv_eq]
    rw [h1]
    exact key V (fd1 V F) (contDiffOn_fd1 hS hSU hV hF) ξ hp
  unfold sumSquares sumSquares1NoDrift
  exact Finset.sum_congr rfl (fun i _ => second (X i) (hX i))

end Joint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The off-diagonal set `{(ξ, η) ∈ C.U × C.U | ξ ≠ η}` of pairs `(ξ, η)`. -/
def kernelOffDiagNoDrift : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
  {p | p.1 ∈ C.U ∧ p.2 ∈ C.U ∧ p.1 ≠ p.2}

theorem isOpen_kernelOffDiagNoDrift : IsOpen C.kernelOffDiagNoDrift :=
  ((C.isOpen_U.preimage continuous_fst).inter ((C.isOpen_U.preimage continuous_snd).inter
    (isOpen_ne_fun continuous_fst continuous_snd)))

/-- The output-cutoff right kernel `Φ(ξ, η) = a(ξ) K(Θ(η, ξ))`, as a function of
the pair `(ξ, η)`. -/
def kernelPhiNoDrift (K a : (Fin (n + m) → ℝ) → ℝ)
    (p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) : ℝ :=
  a p.1 * K (C.Θ p.2 p.1)

variable {C}

theorem contDiffOn_theta_swap_noDrift : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) C.kernelOffDiagNoDrift :=
  C.theta_smooth.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun _ hp => ⟨hp.2.1, hp.1⟩)

theorem contDiffOn_kernelPhi_noDrift {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.kernelPhiNoDrift K a) C.kernelOffDiagNoDrift :=
  (ha.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).mul
    (hK.comp contDiffOn_theta_swap_noDrift
      (fun _ hp => C.theta_ne_zero hp.2.1 hp.1 hp.2.2))

theorem contDiffOn_errorBracket_noDrift {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquares1NoDrift C.Xl (C.kernelPhiNoDrift K a))
      C.kernelOffDiagNoDrift :=
  contDiffOn_sumSquares1_noDrift C.isOpen_kernelOffDiagNoDrift (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi_noDrift hK ha)

/-- For `ξ ≠ η` the bracket of the error kernel is `L̃_ξ` of `a(ξ) Γ(Θ(η, ξ))`
(the right pole formula with `𝓛Γ = 0` off the origin):
`L̃_ξ Φ(ξ, η) = a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`. -/
theorem sumSquares1_kernelPhi_eq_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀)) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U)
    (hne : ξ ≠ η) :
    sumSquares1NoDrift C.Xl (C.kernelPhiNoDrift K a) (ξ, η) =
      a ξ * C.rightPoleErrorNoDrift η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i) a ξ * C.zDeriv η i K (C.Θ η ξ) +
        sumSquares C.Xl a ξ * K (C.Θ η ξ) := by
  have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
  have hp : (ξ, η) ∈ C.kernelOffDiagNoDrift := ⟨hξ, hη, hne⟩
  rw [← sumSquares_slice_fst_noDrift C.isOpen_kernelOffDiagNoDrift (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi_noDrift K.smooth_off_zero ha) hp]
  have h1 := C.sumSquares_mul_comp_theta hη isOpen_compl_singleton K.smooth_off_zero ha
    hξ hΘ
  have h2 : sumSquares C.Y (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) = 0 :=
    sumSquares_kernel_eq_zero_noDrift K hΘ
  change sumSquares C.Xl (fun ξ' => a ξ' * K (C.Θ η ξ')) ξ = _
  rw [h1, h2, zero_add]

end LiftedChart

end RothschildStein.P1
