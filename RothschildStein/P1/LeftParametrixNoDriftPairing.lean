-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixNoDriftAlgebra
public import RothschildStein.P1.RightParametrixNoDriftPole
public import RothschildStein.H1.KernelReflection

/-!
# The model-variable pairing without drift of the left pole computation

The no-drift counterpart of `LeftParametrixPairing`. Without drift the model operator is
`𝓛 = ∑ᵢ Yᵢ²` and the transposed model operator combination of the left pole computation

`T*(α, β, λ) = 𝓛 α + (E*)ᵀ α + ∑ᵢ 2 Zᵢᵀ βᵢ + λ`

is the one of the right pole computation (`LiftedChart.poleTransposeNoDrift`, whose leading term is
`∑ᵢ (Yᵢᵀ)² α`, equal to `𝓛 α` because the model fields are divergence free): the left and the
right differ only in the transported tests `βᵢ = ((a dᵢ + X̃ᵢ a) φ)~` and `λ = ((L̃* a) φ)~`
(`LiftedChart.betaLNoDrift`, `LiftedChart.lamLNoDrift`) and in the kernel, which is now the H1
fundamental kernel `Γ*` of the reversed-drift model `(C.noDriftModel hq ν₀).reverseDrift C.G`. Its
fields are `Fin.cons 0 C.Y` again (`reverseDrift_noDriftModel_fields`: the drift is `0`), so
`𝓛 Γ* = 0` off the origin (`sumSquares_leftKernel_eq_zero_noDrift`) and `∫ Γ* 𝓛ᵀα = α(0)`
(`integral_leftKernel_mul_transpose_noDrift`); this is the pole contribution of the left
parametrix (`integral_kernel_mul_leftPoleTransposeNoDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1
namespace LiftedChart

section Model

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- The fields of the reversed no-drift model are `Fin.cons 0 C.Y` again: the
drift field is `0`, and reversing its sign changes nothing. -/
theorem reverseDrift_noDriftModel_fields (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G) :
    ((C.noDriftModel hq ν₀).reverseDrift C.G).fields =
      (Fin.cons (0 : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) C.Y :
        Fin (q + 1) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [H1.StandingHypotheses.reverseDrift, H1.driftSign]
  · simp [H1.StandingHypotheses.reverseDrift, H1.driftSign, Fin.succ_ne_zero]

/-- The H1 fundamental kernel `Γ*` of the reversed no-drift model is annihilated
by `𝓛 = ∑ᵢ Yᵢ²` off the origin (the pointwise form of `𝓛*Γ* = δ₀` with `𝓛* = 𝓛`). -/
theorem sumSquares_leftKernel_eq_zero_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    {x : Fin (n + m) → ℝ} (hx : x ≠ 0) : sumSquares C.Y K x = 0 := by
  have h := sumSquaresWithDrift_kernel_eq_zero K hx
  rw [reverseDrift_noDriftModel_fields hq ν₀, sumSquaresWithDrift_cons_zero] at h
  exact h

/-- The fundamental property of the reversed no-drift kernel in no-drift form:
`∫ Γ* · ∑ᵢ (Yᵢᵀ)² φ = φ(0)` for tests `φ`. -/
theorem integral_leftKernel_mul_transpose_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    (φ : (Fin (n + m) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, K x * sumSquaresTranspose C.Y φ x) = φ 0 := by
  have h := K.fundamental φ hφ hc
  rw [reverseDrift_noDriftModel_fields hq ν₀] at h
  simp only [sumSquaresWithDriftTranspose_cons_zero] at h
  exact h

end Model

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The first-order coefficient `a dᵢ + X̃ᵢ a` of the left error bracket
(`dᵢ = div X̃ᵢ`), no drift. -/
def leftBetaCoeffNoDrift (a : (Fin (n + m) → ℝ) → ℝ) (i : Fin q) (ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ + fieldDerivative (C.Xl i) a ξ

/-- The bracket of the error kernel of the left parametrix without drift,
`a(ξ) (E_η K)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃* a)(ξ) K(Θ(η, ξ))`
(the no-drift formal adjoint `L̃*` applied in `ξ` to `a(ξ) K(Θ(η, ξ))`). -/
def leftErrBracketNoDrift (K a : (Fin (n + m) → ℝ) → ℝ) (η ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * C.rightPoleErrorNoDrift η K (C.Θ η ξ) +
    2 * ∑ i : Fin q, C.leftBetaCoeffNoDrift a i ξ * C.zDeriv η i K (C.Θ η ξ) +
    sumSquaresTranspose C.Xl a ξ * K (C.Θ η ξ)

variable {C}

theorem contDiffOn_leftBetaCoeffNoDrift {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (i : Fin q) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.leftBetaCoeffNoDrift a i) C.U :=
  (ha.mul (contDiffOn_euclideanDivergence C.chartOpens (C.Xl i)
    (C.contDiffOn_Xl_U i))).add (contDiffOn_fieldDerivative_Xl_noDrift ha i)

theorem contDiffOn_sumSquaresTranspose_XlNoDrift {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresTranspose C.Xl a) C.U := by
  unfold sumSquaresTranspose
  exact ContDiffOn.sum fun i _ => S.contDiffOn_fieldTranspose C.chartOpens (C.Xl i) _
    (C.contDiffOn_Xl_U i)
    (S.contDiffOn_fieldTranspose C.chartOpens (C.Xl i) a (C.contDiffOn_Xl_U i) ha)

variable (C) in
/-- The transported tests `((a dᵢ + X̃ᵢ a) φ)~`. -/
def betaLNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (i : Fin q) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (C.leftBetaCoeffNoDrift a i)
    (contDiffOn_leftBetaCoeffNoDrift ha i) φ)

variable (C) in
/-- The transported test `((L̃* a) φ)~`. -/
def lamLNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (sumSquaresTranspose C.Xl a)
    (contDiffOn_sumSquaresTranspose_XlNoDrift ha) φ)

/-- The pairing of the reversed no-drift fundamental kernel `Γ*` with
`T*(α, β, λ)`: the model part is the pole contribution `α(0)` (`𝓛Γ* = δ₀`). -/
theorem integral_kernel_mul_leftPoleTransposeNoDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, K u * C.poleTransposeNoDrift η α (fun i => β i) lam u) =
      α 0 + (∫ u in (C.e η).target, C.errorOpNoDrift η K u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i η) K u * β i u)) +
      ∫ u in (C.e η).target, K u * lam u := by
  rw [integral_mul_poleTransposeNoDrift hη (errorIbp_kernel_noDrift K hη) α β lam]
  congr 3
  have h := integral_leftKernel_mul_transpose_noDrift K α α.contDiff α.hasCompactSupport
  have hz : ∀ u ∉ (C.e η).target, K u * sumSquaresTranspose C.Y α u = 0 := by
    intro u hu
    have hp := image_eq_zero_of_notMem_tsupport (f := sumSquaresTranspose C.Y α)
      (fun ht => hu (α.tsupport_subset (tsupport_sumSquaresTranspose_subset_noDrift C.Y α ht)))
    rw [hp, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz] at h
  exact h

end LiftedChart

end RothschildStein.P1
