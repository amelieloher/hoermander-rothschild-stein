-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightPoleComputationKernel
public import RothschildStein.P1.RightParametrixTransport

/-!
# The right parametrix kernel and its error kernel are jointly smooth off the diagonal

For the H1 fundamental kernel `Γ`, an output cutoff `a` and `η, ξ ∈ C.U`, `ξ ≠ η`, the function
`Φ(ξ, η) = a(ξ) Γ(Θ(η, ξ))` is jointly smooth on `S₀ = {(ξ, η) ∈ C.U × C.U | ξ ≠ η}`
(`Γ` is smooth off the origin, `Θ` is jointly smooth on `C.U × C.U`, and `Θ(η, ξ) ≠ 0` off the
diagonal). Applying `L̃` in the first variable (`fd1`) keeps joint smoothness, and by the right pole formula
with `𝓛Γ = 0` off the origin

`L̃_ξ Φ(ξ, η) = a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`

(`rightErrorBracket_eq`): the bracket of the error kernel of the right pole computation is jointly
continuous on `S₀`.
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

/-- The derivative of a function of two variables along the field `V` in the
first variable. -/
def fd1 (V : (Fin N → ℝ) → (Fin N → ℝ)) (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  fderiv ℝ F p (V p.1, 0)

theorem fieldDerivative_slice_fst {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {ξ η : Fin N → ℝ} (hF : DifferentiableAt ℝ F (ξ, η)) :
    fieldDerivative V (fun ξ' => F (ξ', η)) ξ = fd1 V F (ξ, η) := by
  unfold fieldDerivative fd1
  have h1 : HasFDerivAt (fun ξ' : Fin N → ℝ => (ξ', η))
      (ContinuousLinearMap.inl ℝ (Fin N → ℝ) (Fin N → ℝ)) ξ := hasFDerivAt_prodMk_left ξ η
  have h2 := hF.hasFDerivAt.comp ξ h1
  have h3 : (fun ξ' : Fin N → ℝ => F (ξ', η)) = F ∘ fun ξ' => (ξ', η) := rfl
  rw [h3, h2.fderiv]
  simp

theorem contDiffOn_fd1 {S : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hS : IsOpen S) {U : Set (Fin N → ℝ)}
    (hSU : ∀ p ∈ S, p.1 ∈ U) {V : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) : ContDiffOn ℝ (⊤ : ℕ∞) (fd1 V F) S := by
  have hVs : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) => V p.1) S :=
    hV.comp contDiff_fst.contDiffOn (fun p hp => hSU p hp)
  exact (hF.fderiv_of_isOpen hS (by simp)).clm_apply (hVs.prodMk contDiffOn_const)

/-- `L̃ = ∑ Xᵢ² + X₀` acting in the first variable of a function of two
variables. -/
def sumSquaresWithDrift1 {q : ℕ} (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  fd1 (X 0) F p + ∑ i : Fin q, fd1 (X i.succ) (fd1 (X i.succ) F) p

theorem contDiffOn_sumSquaresWithDrift1 {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift1 X F) S :=
  (contDiffOn_fd1 hS hSU (hX 0) hF).add (ContDiffOn.sum fun i _ =>
    contDiffOn_fd1 hS hSU (hX i.succ) (contDiffOn_fd1 hS hSU (hX i.succ) hF))

/-- On the slice, `L̃` of `ξ ↦ F(ξ, η)` is `L̃` in the first variable of `F`. -/
theorem sumSquaresWithDrift_slice_fst {q : ℕ} {S : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hS : IsOpen S) {U : Set (Fin N → ℝ)} (hSU : ∀ p ∈ S, p.1 ∈ U)
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    {F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F S)
    {ξ η : Fin N → ℝ} (hp : (ξ, η) ∈ S) :
    sumSquaresWithDrift X (fun ξ' => F (ξ', η)) ξ = sumSquaresWithDrift1 X F (ξ, η) := by
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
  unfold sumSquaresWithDrift sumSquaresWithDrift1
  rw [key (X 0) F hF ξ hp]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => second (X i.succ) (hX i.succ))

end Joint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The off-diagonal set `{(ξ, η) ∈ C.U × C.U | ξ ≠ η}` of pairs `(ξ, η)`. -/
def kernelOffDiag : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
  {p | p.1 ∈ C.U ∧ p.2 ∈ C.U ∧ p.1 ≠ p.2}

theorem isOpen_kernelOffDiag : IsOpen C.kernelOffDiag :=
  ((C.isOpen_U.preimage continuous_fst).inter ((C.isOpen_U.preimage continuous_snd).inter
    (isOpen_ne_fun continuous_fst continuous_snd)))

/-- The output-cutoff right kernel `Φ(ξ, η) = a(ξ) K(Θ(η, ξ))`, as a function of the
pair `(ξ, η)`. -/
def kernelPhi (K a : (Fin (n + m) → ℝ) → ℝ) (p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) : ℝ :=
  a p.1 * K (C.Θ p.2 p.1)

variable {C}

theorem contDiffOn_theta_swap : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) C.kernelOffDiag :=
  C.theta_smooth.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
    (fun _ hp => ⟨hp.2.1, hp.1⟩)

theorem contDiffOn_kernelPhi {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) : ContDiffOn ℝ (⊤ : ℕ∞) (C.kernelPhi K a) C.kernelOffDiag :=
  (ha.comp contDiff_fst.contDiffOn (fun _ hp => hp.1)).mul
    (hK.comp contDiffOn_theta_swap (fun _ hp => C.theta_ne_zero hp.2.1 hp.1 hp.2.2))

theorem contDiffOn_errorBracket {K a : (Fin (n + m) → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ : Set (Fin (n + m) → ℝ)))
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift1 C.Xl (C.kernelPhi K a)) C.kernelOffDiag :=
  contDiffOn_sumSquaresWithDrift1 C.isOpen_kernelOffDiag (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi hK ha)

/-- For `ξ ≠ η` the bracket of the error kernel is `L̃_ξ` of `a(ξ) Γ(Θ(η, ξ))`
(the right pole formula with `𝓛Γ = 0` off the origin):
`L̃_ξ Φ(ξ, η) = a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`. -/
theorem sumSquaresWithDrift1_kernelPhi_eq {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U)
    (hne : ξ ≠ η) :
    sumSquaresWithDrift1 C.Xl (C.kernelPhi K a) (ξ, η) =
      a ξ * C.rightPoleError η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ) := by
  have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
  have hp : (ξ, η) ∈ C.kernelOffDiag := ⟨hξ, hη, hne⟩
  rw [← sumSquaresWithDrift_slice_fst C.isOpen_kernelOffDiag (fun _ hp => hp.1)
    (fun i => C.contDiffOn_Xl_U i) (contDiffOn_kernelPhi K.smooth_off_zero ha) hp]
  have h1 := C.sumSquaresWithDrift_mul_comp_theta hη isOpen_compl_singleton K.smooth_off_zero ha
    hξ hΘ
  have h2 : sumSquaresWithDrift C.Y (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) = 0 :=
    sumSquaresWithDrift_kernel_eq_zero K hΘ
  change sumSquaresWithDrift C.Xl (fun ξ' => a ξ' * K (C.Θ η ξ')) ξ = _
  rw [h1, h2, zero_add]

end LiftedChart

end RothschildStein.P1
