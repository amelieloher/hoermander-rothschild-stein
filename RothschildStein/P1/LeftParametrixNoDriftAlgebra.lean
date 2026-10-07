-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixAlgebra
public import RothschildStein.P1.RightParametrixNoDriftPairing

/-!
# The left pole computation without drift: the formal adjoint `L̃*` applied to `a (g ∘ Θ η)`

The no-drift counterpart of `LeftParametrixAlgebra`. For a lifted chart without drift (alphabet
`Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²` given by `sumSquares C.Xl`), hold the pole `η` fixed and
apply the formal adjoint `L̃* = ∑ᵢ X̃ᵢ² + 2 ∑ dᵢ X̃ᵢ + ∑ (X̃ᵢ dᵢ + dᵢ²)`
(`sumSquaresTranspose`, the no-drift form of the formal adjoint formula: no `X̃₀`, no `d₀`) in the output variable `ξ`
to `a(ξ) g(Θ(η, ξ))` (the pole computation, left parametrix; BB pp. 560–563). With `Rᵢ = R_{[i],η}`,
`Zᵢ = Yᵢ + Rᵢ`, `dᵢ = div X̃ᵢ`, for `g` smooth near `Θ η ξ`:

`L̃*(a g∘Θ η)(ξ) = a(ξ) ((𝓛 g)(u) + (E g)(u)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ g)(u) + (L̃*a)(ξ) g(u)`,

`u = Θ η ξ`, `𝓛 = ∑ Yᵢ²` (`sumSquares C.Y`; it equals its own model adjoint without drift) and
`E = ∑ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²)` (`LiftedChart.rightPoleErrorNoDrift`: without drift the left error
operator is the right one)
(`LiftedChart.sumSquaresTranspose_mul_comp_theta_noDrift`). The pullback of a test function of the
model variable is a test function on the chart (`LiftedChart.pullbackTestNoDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1

section Adjoint

variable {n : ℕ}

/-- The no-drift transpose depends only on the germ. -/
theorem sumSquaresTranspose_congr_of_eventuallyEq {q : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) {φ₁ φ₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : φ₁ =ᶠ[𝓝 x] φ₂) : sumSquaresTranspose X φ₁ x = sumSquaresTranspose X φ₂ x := by
  have h1 : ∀ i, fieldTranspose (X i) φ₁ =ᶠ[𝓝 x] fieldTranspose (X i) φ₂ := fun i =>
    h.eventually_nhds.mono fun y hy => fieldTranspose_congr_of_eventuallyEq (X i) hy
  unfold sumSquaresTranspose
  exact Finset.sum_congr rfl fun i _ => fieldTranspose_congr_of_eventuallyEq (X i) (h1 i)

/-- The zeroth-order coefficient of the no-drift formal adjoint `L̃*`:
`c = ∑ᵢ (X̃ᵢ dᵢ + dᵢ²)`, `dᵢ = div X̃ᵢ` (no `d₀` term). -/
def adjointCoeffNoDrift {q : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (X i) (Hormander.Interface.euclideanDivergence (X i)) x +
    Hormander.Interface.euclideanDivergence (X i) x ^ 2)

/-- Product formula for the no-drift `L̃*` on an open set:
`L̃*(a g) = a L̃*g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃*a − c a) g`, `c = ∑ᵢ (X̃ᵢ dᵢ + dᵢ²)`. -/
theorem sumSquaresTranspose_mul_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {a g : (Fin n → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin n → ℝ))) {x : Fin n → ℝ}
    (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    sumSquaresTranspose X (fun y => a y * g y) x =
      a x * sumSquaresTranspose X g x +
        2 * ∑ i : Fin q, fieldDerivative (X i) a x * fieldDerivative (X i) g x +
        (sumSquaresTranspose X a x - a x * adjointCoeffNoDrift X x) * g x := by
  have hsq := fun i : Fin q => fieldTranspose_square_mul_apply Ω (hX i) ha hg hx
  unfold sumSquaresTranspose adjointCoeffNoDrift
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

end Adjoint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- The chain rule for the no-drift formal adjoint `L̃*` at a point: for
`η, ξ ∈ C.U` and `g` smooth on an open `W ∋ Θ η ξ`,
`L̃*(g∘Θ η)(ξ) = ((𝓛 + E) g)(Θ η ξ) + 2 ∑ᵢ dᵢ(ξ) (Zᵢ g)(Θ η ξ) + c(ξ) g(Θ η ξ)`. -/
theorem sumSquaresTranspose_comp_theta_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresTranspose C.Xl (g ∘ C.Θ η) ξ =
      sumSquares C.Y g (C.Θ η ξ) + C.rightPoleErrorNoDrift η g (C.Θ η ξ) +
        2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (C.Xl i) ξ *
          C.zDeriv η i g (C.Θ η ξ) + adjointCoeffNoDrift C.Xl ξ * g (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hgΘ := C.contDiffOn_comp_theta hη hg
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (C.U ∩ C.Θ η ⁻¹' W) :=
    fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left
  have hdiff := differentiableAt_of_contDiffOn_isOpen hW hg hξW
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i hξ hdiff
  have happ := sumSquaresTranspose_apply (⟨_, hO⟩ : Opens (Fin (n + m) → ℝ)) C.Xl hX
    (g ∘ C.Θ η) hgΘ hξO
  have hcr := C.sumSquares_comp_theta hη hW hg hξ hξW
  have h1 : ∑ i : Fin q, fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) (g ∘ C.Θ η)) ξ =
      sumSquares C.Xl (g ∘ C.Θ η) ξ := rfl
  rw [happ, h1, hcr]
  simp only [hz, Function.comp_apply, adjointCoeffNoDrift, ← Finset.sum_mul]

/-- The left output product formula for `L̃*` without drift, with the pole
`η` fixed: for `a` smooth on `C.U`, `η, ξ ∈ C.U` and `g` smooth on an open `W ∋ Θ η ξ`,
`L̃*(a g∘Θ η)(ξ) = a(ξ) ((𝓛 g)(u) + (E g)(u)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ g)(u) + (L̃*a)(ξ) g(u)`,
`u = Θ η ξ`, `dᵢ = div X̃ᵢ`. -/
theorem sumSquaresTranspose_mul_comp_theta_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresTranspose C.Xl (fun ξ' => a ξ' * g (C.Θ η ξ')) ξ =
      a ξ * (sumSquares C.Y g (C.Θ η ξ) + C.rightPoleErrorNoDrift η g (C.Θ η ξ)) +
        2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ +
          fieldDerivative (C.Xl i) a ξ) * C.zDeriv η i g (C.Θ η ξ) +
        sumSquaresTranspose C.Xl a ξ * g (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hgΘ := C.contDiffOn_comp_theta hη hg
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hmul := sumSquaresTranspose_mul_noDrift (⟨_, hO⟩ : Opens (Fin (n + m) → ℝ)) C.Xl
    (fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left) (ha.mono inter_subset_left) hgΘ hξO
  have hcr := C.sumSquaresTranspose_comp_theta_noDrift hη hW hg hξ hξW
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i hξ
    (differentiableAt_of_contDiffOn_isOpen hW hg hξW)
  have hmul' : sumSquaresTranspose C.Xl (fun y => a y * g (C.Θ η y)) ξ =
      a ξ * sumSquaresTranspose C.Xl (g ∘ C.Θ η) ξ +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i) a ξ *
          fieldDerivative (C.Xl i) (g ∘ C.Θ η) ξ +
        (sumSquaresTranspose C.Xl a ξ - a ξ * adjointCoeffNoDrift C.Xl ξ) * g (C.Θ η ξ) := hmul
  have hs : ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ +
      fieldDerivative (C.Xl i) a ξ) * C.zDeriv η i g (C.Θ η ξ) =
      a ξ * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (C.Xl i) ξ *
        C.zDeriv η i g (C.Θ η ξ) +
      ∑ i : Fin q, fieldDerivative (C.Xl i) a ξ * C.zDeriv η i g (C.Θ η ξ) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hmul', hcr, hs]
  simp only [hz]
  ring

end LiftedChart

section TestFunctions

variable {n : ℕ}

/-- `L̃ ψ = ∑ᵢ X̃ᵢ² ψ` of a test function is a test function (no drift). -/
def sumSquaresTestNoDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  ∑ i : Fin q, fieldDerivativeTest Ω (X i) (hX i) (fieldDerivativeTest Ω (X i) (hX i) ψ)

theorem sumSquaresTestNoDrift_coe {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (sumSquaresTestNoDrift Ω X hX ψ : (Fin n → ℝ) → ℝ) = sumSquares X ψ := by
  funext x
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h : (sumSquaresTestNoDrift Ω X hX ψ : (Fin n → ℝ) → ℝ) x =
      ev (∑ i : Fin q, fieldDerivativeTest Ω (X i) (hX i)
        (fieldDerivativeTest Ω (X i) (hX i) ψ)) := rfl
  rw [h, map_sum]
  unfold sumSquares
  simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fieldDerivativeTest_apply]
  rfl

end TestFunctions

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

section Pullback

theorem isCompact_symm_image_tsupport_noDrift {η : Fin (n + m) → ℝ}
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    IsCompact ((C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ)) :=
  g.hasCompactSupport.image_of_continuousOn ((C.e η).continuousOn_symm.mono g.tsupport_subset)

theorem symm_image_tsupport_subset_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := by
  rintro _ ⟨u, hu, rfl⟩
  have := (C.e η).map_target (g.tsupport_subset hu)
  rwa [e_source hη] at this

theorem comp_theta_eq_zero_of_notMem_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) {ξ : Fin (n + m) → ℝ} (hξU : ξ ∈ C.U)
    (hξ : ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ)) : g (C.Θ η ξ) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hξ ⟨_, h, symm_theta hη hξU⟩

/-- The pullback `ξ ↦ a(ξ) g(Θ(η, ξ))` (extended by zero off `C.U`) of a test
function `g` of the model variable is a test function on the chart (its support lies in the
compact set `(e η)⁻¹ (supp g) ⊆ C.U`), no drift. -/
def pullbackTestNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := by
  have hKc := isCompact_symm_image_tsupport_noDrift (C := C) g
  have hKU := symm_image_tsupport_subset_noDrift hη g
  have hz : ∀ ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ),
      C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) ξ = 0 := fun ξ hξ => by
    by_cases hξU : ξ ∈ C.U
    · rw [indicator_of_mem hξU]
      simp [comp_theta_eq_zero_of_notMem_noDrift hη g hξU hξ]
    · rw [indicator_of_notMem hξU]
  refine ⟨C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)), ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun ξ => ?_
    by_cases hξU : ξ ∈ C.U
    · have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => a ξ * g (C.Θ η ξ)) C.U :=
        ha.mul (g.contDiff.comp_contDiffOn (C.contDiffOn_theta hη))
      have he : C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) =ᶠ[𝓝 ξ]
          fun ξ => a ξ * g (C.Θ η ξ) :=
        Filter.eventuallyEq_of_mem (C.isOpen_U.mem_nhds hξU) (fun y hy => indicator_of_mem hy _)
      exact (hF.contDiffAt (C.isOpen_U.mem_nhds hξU)).congr_of_eventuallyEq he
    · have hξK : ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ) :=
        fun h => hξU (hKU h)
      have hev : ∀ᶠ y in 𝓝 ξ, C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) y = 0 := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hξK] with y hy
        exact hz y hy
      exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin (n + m) → ℝ => (0 : ℝ)) ξ
        ).congr_of_eventuallyEq hev
  · exact HasCompactSupport.intro hKc hz
  · refine (closure_minimal (fun ξ hξ => ?_) hKc.isClosed).trans hKU
    by_contra h
    exact hξ (hz ξ h)

theorem pullbackTestNoDrift_apply {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    pullbackTestNoDrift hη ha g ξ = a ξ * g (C.Θ η ξ) := by
  show C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) ξ = _
  exact indicator_of_mem hξ _

end Pullback

end LiftedChart

end RothschildStein.P1
