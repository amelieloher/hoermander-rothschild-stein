-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesLetters
public import RothschildStein.P1.ErrorTypesTranspose
public import RothschildStein.P1.ParametrixStatementsPrincipal
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.ParametrixStatementsNoDrift
public import RothschildStein.P1.LeftParametrixNoDriftPairing
public import RothschildStein.P1.RightParametrixNoDriftPairing

/-!
# Parametrix error types: the error kernel of the left parametrix without drift

The no-drift analogue of `ErrorTypesLeft` (`L̃ = ∑ᵢ X̃ᵢ²`, all weights one, no drift remainder): the error
kernel `(b(η) / c(η)) [a(ξ) (E_η K)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃* a)(ξ) K(Θ(η, ξ))]`,
`E = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²)` (`LiftedChart.leftErrorKernelNoDrift`), is a kernel of type `1` modeled on the pole
`K = Γ*` of every frame of the chart (`isTypeKernelOn_leftErrorKernelNoDrift`), and
`parametrixErrorTypesNoDrift_of_isStandardFrame` is the exact step `ParametrixErrorTypesNoDrift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- The algebra of the assembly of the no-drift left error kernel. -/
theorem leftErrorNoDrift_assembly_algebra {q : ℕ} (β a γ P : ℝ) (E₁ E₂ E₃ B Z : Fin q → ℝ) :
    (∑ i, (a * β * (E₁ i + E₂ i + E₃ i) + 2 * (B i * β * Z i))) + γ * β * P =
      β * (a * (∑ i, (E₁ i + E₂ i + E₃ i)) + 2 * ∑ i, B i * Z i + γ * P) := by
  have h1 : ∑ i, (a * β * (E₁ i + E₂ i + E₃ i) + 2 * (B i * β * Z i)) =
      (a * β) * ∑ i, (E₁ i + E₂ i + E₃ i) + (2 * β) * ∑ i, B i * Z i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The explicit error kernel of the left parametrix of a lifted no-drift chart is a kernel
of type `1` modeled on the pole `K = F.Γs` of any frame `F` of the chart, for cutoffs `a, b ∈ C_c^∞(F.V)`. -/
theorem isTypeKernelOn_leftErrorKernelNoDrift (F : KernelFrame (n + m)) (hF : C.IsLiftedFrame F)
    (K : (Fin (n + m) → ℝ) → ℝ) (hK : F.Γs = K) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F true 1 (fun ξ η => C.leftErrorKernelNoDrift K a b ξ η) := by
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
      (Hormander.Interface.euclideanDivergence (C.Xl i)) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (contDiffOn_euclideanDivergence C.chartOpens (C.Xl i)
      (C.contDiffOn_Xl_U i)).mono hVU
  let B : Fin q → TestFunction F.V ℝ (⊤ : ℕ∞) := fun i =>
    testMultiplierOn F.V (Hormander.Interface.euclideanDivergence (C.Xl i)) (hdiv i) a +
      fieldDerivativeTest F.V (C.Xl i) (hX i) a
  have hB : ∀ i ξ, B i ξ = C.leftBetaCoeffNoDrift a i ξ := fun i ξ => rfl
  let γ : TestFunction F.V ℝ (⊤ : ℕ∞) := sumSquaresTransposeTest F.V C.Xl hX a
  have hγ : ∀ ξ, γ ξ = sumSquaresTranspose C.Xl a ξ := fun ξ =>
    congrFun (sumSquaresTransposeTest_coe_noDrift F.V C.Xl hX a) ξ
  have hw1 : ∀ i : Fin q, ((((fun _ : Fin q => (1 : ℕ+)) i : ℕ+)) : ℕ) = 1 := fun i => rfl
  have TA := fun i : Fin q => C.isTypeKernelOn_horizontal_poleError F hΘ hG hVU true i (hw1 i) hΓ
    hhom a β
  have TB := fun i : Fin q => C.isTypeKernelOn_horizontal_zDeriv F hΘ hG hVU true i (hw1 i) hΓ
    hhom (B i) β
  have TG : IsTypeKernelOn F true 1 (fun ξ η => γ ξ * β η * F.pole true (F.Θ η ξ)) :=
    (isTypeKernelOn_of_eq_principal F (lam := 2) le_rfl γ β true
      (fun ξ η => γ ξ * β η * F.pole true (F.Θ η ξ)) (fun ξ η => rfl)).mono (by norm_num)
  have hS := (IsTypeKernelOn.sum (Finset.univ : Finset (Fin q))
      (fun i _ => (TA i).add ((TB i).smul 2))).add TG
  refine hS.congr_all fun ξ η => ?_
  subst hK
  simp only [leftErrorKernelNoDrift, leftErrBracketNoDrift, rightPoleErrorNoDrift, zDeriv, hβ, hB,
    hγ, hΘ, hp]
  exact leftErrorNoDrift_assembly_algebra _ _ _ _ _ _ _ _ _

variable {C}

/-- The step `ParametrixErrorTypesNoDrift` for every standard frame of a lifted no-drift chart
(BB pp. 561–563, the pole computation): the negated error kernel `F₁ = -E₁` is a kernel of type `1`
modeled on `Γ*`, and its transpose, the kernel of `F₂ = F₁ᵗ`, is a kernel of type `1` modeled on `Γ`. -/
theorem parametrixErrorTypesNoDrift_of_isStandardFrame (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (Γ : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) {F : KernelFrame (n + m)}
    (hF : C.IsStandardFrame F (C.noDriftModel hq ν₀) Γ hQ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    ParametrixErrorTypesNoDrift C F hq ν₀ Γ hQ a b := by
  intro _
  have h1 : IsTypeKernelOn F true 1
      (fun ξ η => -C.leftErrorKernelNoDrift (Γ.reflection hQ) a b ξ η) :=
    (C.isTypeKernelOn_leftErrorKernelNoDrift F hF.lifted (Γ.reflection hQ) hF.Γs_eq a b).neg
  refine ⟨h1, ?_⟩
  have hΓs : ∀ u : Fin (n + m) → ℝ, u ≠ 0 → F.Γs u = F.Γ (-u) := fun u _ => by
    rw [hF.Γs_eq, hF.Γ_eq]
    exact Γ.reflection_neg hQ (fun x => C.inv_eq_neg x) u
  exact C.isTypeKernelOn_transpose F hF.lifted.Θ_eq (subset_closure.trans hF.lifted.closure_subset)
    hΓs hF.lifted.Γ_smooth hF.lifted.Γs_smooth true 1 _ h1

end LiftedChart

end RothschildStein.P1
