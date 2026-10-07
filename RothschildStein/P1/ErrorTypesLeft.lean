-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesLetters
public import RothschildStein.P1.ErrorTypesTranspose
public import RothschildStein.P1.ParametrixStatementsPrincipal
public import RothschildStein.P1.LeftParametrixPole
public import RothschildStein.P1.RightParametrixPairing
public import RothschildStein.P1.StandardFrame

/-!
# Parametrix error types: the error kernel of the left parametrix with drift

The explicit error kernel of the left parametrix of a lifted drift chart (computed by applying `L̃*` to the pole; BB
Thm 11.25, pp. 560-563)

`e(ξ, η) = (b(η) / c(η)) [a(ξ) (E*_η K)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃* a)(ξ) K(Θ(η, ξ))]`,

`E* = ∑_{i ≥ 1} (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) - R₀` (`LiftedChart.leftErrorKernel`), is a kernel of type `1` modeled on
the pole `K = Γ*` of the frame (`LiftedChart.isTypeKernelOn_leftErrorKernel`), for every frame of the chart
(`IsLiftedFrame`) whose second pole is `K`: the second-order terms have local degrees `1, 1, 0`, the drift
remainder `R₀` degree `1`, the first-order terms degrees `1, 0` and the zeroth-order term degree `0`; the
cutoffs `a`, `b / c`, `a dᵢ + X̃ᵢ a`, `L̃* a` are test functions of the cutoff region.

`LiftedChart.parametrixErrorTypes_of_isStandardFrame` is the exact step `ParametrixErrorTypes`: the negated kernel is of type
`1` modeled on `Γ*` and its transpose, the kernel of `F₂ = F₁ᵗ`, of type `1` modeled on `Γ` (the transpose
swaps the pole, `Γ*(u) = Γ(-u)`, `isTypeKernelOn_transpose`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- The algebra of the assembly of the left error kernel: the bracket
`a (∑ᵢ (E₁ + E₂ + E₃) - E₀) + 2 ∑ᵢ B Z + γ P` weighted by `β` is the sum of the weighted terms. -/
theorem leftError_assembly_algebra {q : ℕ} (β a γ R₀ P : ℝ) (E₁ E₂ E₃ B Z : Fin q → ℝ) :
    (∑ i, (a * β * (E₁ i + E₂ i + E₃ i) + 2 * (B i * β * Z i))) + -(a * β * R₀) + γ * β * P =
      β * (a * ((∑ i, (E₁ i + E₂ i + E₃ i)) - R₀) + 2 * ∑ i, B i * Z i + γ * P) := by
  have h1 : ∑ i, (a * β * (E₁ i + E₂ i + E₃ i) + 2 * (B i * β * Z i)) =
      (a * β) * ∑ i, (E₁ i + E₂ i + E₃ i) + (2 * β) * ∑ i, B i * Z i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The explicit error kernel of the left parametrix of a lifted drift chart is a kernel of
type `1` modeled on the pole `K = F.Γs` of any frame `F` of the chart, for cutoffs `a, b ∈ C_c^∞(F.V)`
(BB pp. 561-563: local degrees at most `1, 1, 0, 1`, hence types at least `1, 1, 2, 1`). -/
theorem isTypeKernelOn_leftErrorKernel (F : KernelFrame (n + m)) (hF : C.IsLiftedFrame F)
    (K : (Fin (n + m) → ℝ) → ℝ) (hK : F.Γs = K) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F true 1 (fun ξ η => C.leftErrorKernel K a b ξ η) := by
  have hΘ := hF.Θ_eq
  have hG := hF.G_eq
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  have hΓ := hF.pole_smooth true
  have hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole true (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole true u :=
    fun r hr u hu => by
      rw [hG]
      exact hF.pole_homogeneous true r hr u hu
  have hp : F.pole true = K := hK
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hVU
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) C.c (F.V : Set (Fin (n + m) → ℝ)) :=
    C.density_smooth.mono hVU
  have hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < C.c ξ :=
    fun ξ hξ => C.density_pos ξ (hVU hξ)
  let β : TestFunction F.V ℝ (⊤ : ℕ∞) := divTest F C.c hc hc0 b
  have hβ : ∀ ξ, β ξ = b ξ / C.c ξ := divTest_apply F C.c hc hc0 b
  have hdiv : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (Hormander.Interface.euclideanDivergence (C.Xl i.succ)) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (contDiffOn_euclideanDivergence C.chartOpens (C.Xl i.succ)
      (C.contDiffOn_Xl_U i.succ)).mono hVU
  let B : Fin q → TestFunction F.V ℝ (⊤ : ℕ∞) := fun i =>
    testMultiplierOn F.V (Hormander.Interface.euclideanDivergence (C.Xl i.succ)) (hdiv i) a +
      fieldDerivativeTest F.V (C.Xl i.succ) (hX i.succ) a
  have hB : ∀ i ξ, B i ξ = C.leftBetaCoeff a i ξ := fun i ξ => rfl
  let γ : TestFunction F.V ℝ (⊤ : ℕ∞) := sumSquaresWithDriftTransposeTest F.V C.Xl hX a
  have hγ : ∀ ξ, γ ξ = sumSquaresWithDriftTranspose C.Xl a ξ := fun ξ =>
    congrFun (sumSquaresWithDriftTransposeTest_coe F.V C.Xl hX a) ξ
  have hw1 : ∀ i : Fin q, ((((fun j : Fin (q + 1) => if j = 0 then (2 : ℕ+) else 1) i.succ : ℕ+)) : ℕ)
      = 1 := fun i => by simp
  have hw0 : ((((fun j : Fin (q + 1) => if j = 0 then (2 : ℕ+) else 1) 0 : ℕ+)) : ℕ) ≤ 2 := by
    simp
  have TA := fun i : Fin q => C.isTypeKernelOn_horizontal_poleError F hΘ hG hVU true i.succ (hw1 i) hΓ
    hhom a β
  have TB := fun i : Fin q => C.isTypeKernelOn_horizontal_zDeriv F hΘ hG hVU true i.succ (hw1 i) hΓ
    hhom (B i) β
  have T0 := C.isTypeKernelOn_remainder_term F hΘ hG hVU true 0 hw0 hΓ hhom a β
  have TG : IsTypeKernelOn F true 1 (fun ξ η => γ ξ * β η * F.pole true (F.Θ η ξ)) :=
    (isTypeKernelOn_of_eq_principal F (lam := 2) le_rfl γ β true
      (fun ξ η => γ ξ * β η * F.pole true (F.Θ η ξ)) (fun ξ η => rfl)).mono (by norm_num)
  have hS := ((IsTypeKernelOn.sum (Finset.univ : Finset (Fin q))
      (fun i _ => (TA i).add ((TB i).smul 2))).add T0.neg).add TG
  refine hS.congr_all fun ξ η => ?_
  subst hK
  simp only [leftErrorKernel, leftErrBracket, leftPoleError, zDeriv, hβ, hB, hγ, hΘ, hp]
  exact leftError_assembly_algebra _ _ _ _ _ _ _ _ _ _

variable {C}

/-- The step `ParametrixErrorTypes` for every standard frame of a lifted drift chart (BB
pp. 561–563, the pole computation): the negated error kernel `F₁ = -E₁` is a kernel of type `1` modeled on
`Γ*`, and its transpose, the kernel of `F₂ = F₁ᵗ`, is a kernel of type `1` modeled on `Γ`. -/
theorem parametrixErrorTypes_of_isStandardFrame (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (Γ : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) {F : KernelFrame (n + m)}
    (hF : C.IsStandardFrame F (C.driftModel hq ν₀) Γ hQ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    ParametrixErrorTypes C F hq ν₀ Γ hQ a b := by
  intro _
  have h1 : IsTypeKernelOn F true 1 (fun ξ η => -C.leftErrorKernel (Γ.reflection hQ) a b ξ η) :=
    (C.isTypeKernelOn_leftErrorKernel F hF.lifted (Γ.reflection hQ) hF.Γs_eq a b).neg
  refine ⟨h1, ?_⟩
  have hΓs : ∀ u : Fin (n + m) → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u) := fun u _ => by
    rw [hF.Γs_eq, hF.Γ_eq]
    exact Γ.reflection_neg hQ (fun x => C.inv_eq_neg x) u
  exact C.isTypeKernelOn_transpose F hF.lifted.Θ_eq (subset_closure.trans hF.lifted.closure_subset)
    hΓs hF.lifted.Γ_smooth hF.lifted.Γs_smooth true 1 _ h1

end LiftedChart

end RothschildStein.P1
