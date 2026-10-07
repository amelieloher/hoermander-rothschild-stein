-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.AdjointExpansionChart
public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.P1.RightParametrixError

/-!
# The left pole computation: the formal adjoint `L̃*` applied to `a (g ∘ Θ η)`

Hold the pole `η` fixed and apply the formal adjoint `L̃* = ∑ᵢ X̃ᵢ² − X̃₀ + 2 ∑ dᵢ X̃ᵢ +
∑ (X̃ᵢ dᵢ + dᵢ²) − d₀` (`sumSquaresWithDriftTranspose`) in the output variable `ξ` to
`a(ξ) g(Θ(η, ξ))` (the pole computation, left parametrix; BB pp. 560–563, with the sign erratum:
the drift remainder enters with the **negative** sign). With `Rᵢ = R_{[i],η}`, `Zᵢ = Yᵢ + Rᵢ`,
`dᵢ = div X̃ᵢ`, for `g` smooth near `Θ η ξ`:

`L̃*(a g∘Θ η)(ξ) = a(ξ) ((𝓛* g)(u) + (E* g)(u)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ g)(u) + (L̃*a)(ξ) g(u)`,

`u = Θ η ξ`, `𝓛* = ∑ Yᵢ² − Y₀` (`LiftedChart.modelAdjoint`) and
`E* = ∑ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) − R₀` (`LiftedChart.leftPoleError`)
(`LiftedChart.sumSquaresWithDriftTranspose_mul_comp_theta`). The pullback of a test function of the
model variable is a test function on the chart (`LiftedChart.pullbackTest`).
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

/-- The scalar transpose depends only on the germ. -/
theorem fieldTranspose_congr_of_eventuallyEq (V : (Fin n → ℝ) → (Fin n → ℝ))
    {φ₁ φ₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : φ₁ =ᶠ[𝓝 x] φ₂) :
    fieldTranspose V φ₁ x = fieldTranspose V φ₂ x := by
  have h' : (fun y => φ₁ y • V y) =ᶠ[𝓝 x] fun y => φ₂ y • V y :=
    h.mono fun y hy => by simp [hy]
  unfold fieldTranspose Hormander.Interface.euclideanDivergence
  rw [h'.fderiv_eq]

/-- The transpose `L̃*` depends only on the germ. -/
theorem sumSquaresWithDriftTranspose_congr_of_eventuallyEq {q : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) {φ₁ φ₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : φ₁ =ᶠ[𝓝 x] φ₂) :
    sumSquaresWithDriftTranspose X φ₁ x = sumSquaresWithDriftTranspose X φ₂ x := by
  have h1 : ∀ i, fieldTranspose (X i) φ₁ =ᶠ[𝓝 x] fieldTranspose (X i) φ₂ := fun i =>
    h.eventually_nhds.mono fun y hy => fieldTranspose_congr_of_eventuallyEq (X i) hy
  unfold sumSquaresWithDriftTranspose
  rw [fieldTranspose_congr_of_eventuallyEq (X 0) h]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    fieldTranspose_congr_of_eventuallyEq (X i.succ) (h1 i.succ)

/-- The zeroth-order coefficient of the formal adjoint `L̃*`:
`c = ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) − d₀`, `dᵢ = div X̃ᵢ`. -/
def adjointCoeff {q : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (X i.succ) (Hormander.Interface.euclideanDivergence (X i.succ)) x +
      Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) -
    Hormander.Interface.euclideanDivergence (X 0) x

/-- First-order transpose product formula on an open set:
`Vᵀ(a g) = a Vᵀg + (Vᵀa + a div V) g`. -/
theorem fieldTranspose_mul_apply (Ω : Opens (Fin n → ℝ)) {V : (Fin n → ℝ) → (Fin n → ℝ)}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) {a g : (Fin n → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin n → ℝ))) {x : Fin n → ℝ}
    (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    fieldTranspose V (fun y => a y * g y) x =
      a x * fieldTranspose V g x +
        (fieldTranspose V a x + a x * Hormander.Interface.euclideanDivergence V x) * g x := by
  have hVd : DifferentiableAt ℝ V x := differentiableAt_of_contDiffOn_isOpen Ω.isOpen hV hx
  rw [S.fieldTranspose_mul V a g x hVd (differentiableAt_of_contDiffOn_isOpen Ω.isOpen ha hx)
    (differentiableAt_of_contDiffOn_isOpen Ω.isOpen hg hx),
    S.fieldTranspose_formula V a x hVd (differentiableAt_of_contDiffOn_isOpen Ω.isOpen ha hx)]
  ring

/-- Product formula for the square of a field transpose on an open set:
`(Vᵀ)²(a g) = a (Vᵀ)²g + 2 (V a)(V g) + ((Vᵀ)²a − a (V d + d²)) g`, `d = div V`. -/
theorem fieldTranspose_square_mul_apply (Ω : Opens (Fin n → ℝ)) {V : (Fin n → ℝ) → (Fin n → ℝ)}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) {a g : (Fin n → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin n → ℝ))) {x : Fin n → ℝ}
    (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    fieldTranspose V (fieldTranspose V (fun y => a y * g y)) x =
      a x * fieldTranspose V (fieldTranspose V g) x +
        2 * (fieldDerivative V a x * fieldDerivative V g x) +
        (fieldTranspose V (fieldTranspose V a) x -
          a x * (fieldDerivative V (Hormander.Interface.euclideanDivergence V) x +
            Hormander.Interface.euclideanDivergence V x ^ 2)) * g x := by
  rw [fieldTranspose_fieldTranspose_apply Ω V hV (fun y => a y * g y) (ha.mul hg) hx,
    fieldTranspose_fieldTranspose_apply Ω V hV g hg hx,
    fieldTranspose_fieldTranspose_apply Ω V hV a ha hx,
    fieldDerivative_square_mul_pointwise Ω.isOpen hV ha hg hx,
    S.fieldDerivative_mul V a g x (differentiableAt_of_contDiffOn_isOpen Ω.isOpen ha hx)
      (differentiableAt_of_contDiffOn_isOpen Ω.isOpen hg hx)]
  ring

/-- Product formula for `L̃*` on an open set:
`L̃*(a g) = a L̃*g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃*a − c a) g`, `c = ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) − d₀`. -/
theorem sumSquaresWithDriftTranspose_mul {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {a g : (Fin n → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin n → ℝ))) {x : Fin n → ℝ}
    (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    sumSquaresWithDriftTranspose X (fun y => a y * g y) x =
      a x * sumSquaresWithDriftTranspose X g x +
        2 * ∑ i : Fin q, fieldDerivative (X i.succ) a x * fieldDerivative (X i.succ) g x +
        (sumSquaresWithDriftTranspose X a x - a x * adjointCoeff X x) * g x := by
  have hsq := fun i : Fin q => fieldTranspose_square_mul_apply Ω (hX i.succ) ha hg hx
  unfold sumSquaresWithDriftTranspose adjointCoeff
  rw [fieldTranspose_mul_apply Ω (hX 0) ha hg hx, Finset.sum_congr rfl (fun i _ => hsq i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end Adjoint

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The model adjoint `𝓛* g = ∑_{i ≥ 1} Yᵢ² g − Y₀ g` (the model part of the left
pole computation; `Γ*` is its fundamental kernel). -/
def modelAdjoint (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, fieldDerivative (C.Y i.succ) (fieldDerivative (C.Y i.succ) g) u -
    fieldDerivative (C.Y 0) g u

/-- The differential error of the left pole computation, before the output
cutoff and the divergence terms:
`E* = ∑_{i ≥ 1} (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) − R₀`, `Rᵢ = R_{[i],η}`; the drift remainder `R₀` enters with
the **negative** sign (correcting BB pp. 561, 563). -/
def leftPoleError (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u +
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (C.Y i.succ) g) u +
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (C.R [i.succ] η) g) u) -
    fieldDerivative (C.R [0] η) g u

/-- The left error operator in composite form
`E* g = ∑_{i ≥ 1} (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g)) − R₀ g`. -/
def leftErrorOp (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) : ℝ :=
  C.errorOp η g u - 2 * fieldDerivative (C.R [0] η) g u

/-- The transpose of the left error operator,
`(E*)ᵀ φ = Eᵀ φ − 2 R₀ᵀ φ`. -/
def leftErrorTranspose (η : Fin (n + m) → ℝ) (φ : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  C.errorTranspose η φ u - 2 * fieldTranspose (C.R [0] η) φ u

variable {C}

/-- The explicit left error is the composite left error on functions smooth near
a point of the target of `e η`. -/
theorem leftPoleError_eq_leftErrorOp {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {u : Fin (n + m) → ℝ} (huW : u ∈ W)
    (hut : u ∈ (C.e η).target) : C.leftPoleError η g u = C.leftErrorOp η g u := by
  have h := C.rightPoleError_eq_errorOp hη hW hg huW hut
  unfold leftPoleError leftErrorOp
  unfold rightPoleError at h
  linarith

/-- The chain rule for the formal adjoint `L̃*` at a point: for
`η, ξ ∈ C.U` and `g` smooth on an open `W ∋ Θ η ξ`,
`L̃*(g∘Θ η)(ξ) = ((𝓛* + E*) g)(Θ η ξ) + 2 ∑ᵢ dᵢ(ξ) (Zᵢ g)(Θ η ξ) + c(ξ) g(Θ η ξ)`. -/
theorem sumSquaresWithDriftTranspose_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresWithDriftTranspose C.Xl (g ∘ C.Θ η) ξ =
      C.modelAdjoint g (C.Θ η ξ) + C.leftPoleError η g (C.Θ η ξ) +
        2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ *
          C.zDeriv η i.succ g (C.Θ η ξ) + adjointCoeff C.Xl ξ * g (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hgΘ := C.contDiffOn_comp_theta hη hg
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (C.U ∩ C.Θ η ⁻¹' W) :=
    fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left
  have hdiff := differentiableAt_of_contDiffOn_isOpen hW hg hξW
  have h0 : fieldDerivative (C.Xl 0) (g ∘ C.Θ η) ξ =
      fieldDerivative (C.Y 0) g (C.Θ η ξ) + fieldDerivative (C.R [0] η) g (C.Θ η ξ) :=
    C.fieldDerivative_comp_theta hη 0 hξ hdiff
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i.succ hξ hdiff
  have hi := fun i : Fin q =>
    C.fieldDerivative_fieldDerivative_comp_theta_expand hη i.succ hW hg hξ hξW
  have hd0 := S.fieldTranspose_formula (C.Xl 0) (g ∘ C.Θ η) ξ
    (differentiableAt_of_contDiffOn_isOpen hO (hX 0) hξO)
    (differentiableAt_of_contDiffOn_isOpen hO hgΘ hξO)
  have hsq := fun i : Fin q => fieldTranspose_fieldTranspose_apply
    (⟨_, hO⟩ : Opens (Fin (n + m) → ℝ)) (C.Xl i.succ) (hX i.succ) (g ∘ C.Θ η) hgΘ hξO
  unfold sumSquaresWithDriftTranspose
  rw [hd0, Finset.sum_congr rfl (fun i _ => hsq i)]
  simp only [adjointCoeff, modelAdjoint, leftPoleError, h0, hz, hi, Function.comp_apply, zDeriv]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The left output product formula for `L̃*` with the pole `η` fixed: for `a`
smooth on `C.U`, `η, ξ ∈ C.U` and `g` smooth on an open `W ∋ Θ η ξ`,
`L̃*(a g∘Θ η)(ξ) = a(ξ) ((𝓛* g)(u) + (E* g)(u)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ g)(u) + (L̃* a)(ξ) g(u)`,
`u = Θ η ξ`, `dᵢ = div X̃ᵢ`. -/
theorem sumSquaresWithDriftTranspose_mul_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresWithDriftTranspose C.Xl (fun ξ' => a ξ' * g (C.Θ η ξ')) ξ =
      a ξ * (C.modelAdjoint g (C.Θ η ξ) + C.leftPoleError η g (C.Θ η ξ)) +
        2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
          fieldDerivative (C.Xl i.succ) a ξ) * C.zDeriv η i.succ g (C.Θ η ξ) +
        sumSquaresWithDriftTranspose C.Xl a ξ * g (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hgΘ := C.contDiffOn_comp_theta hη hg
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hmul := sumSquaresWithDriftTranspose_mul (⟨_, hO⟩ : Opens (Fin (n + m) → ℝ)) C.Xl
    (fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left) (ha.mono inter_subset_left) hgΘ hξO
  have hcr := C.sumSquaresWithDriftTranspose_comp_theta hη hW hg hξ hξW
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i.succ hξ
    (differentiableAt_of_contDiffOn_isOpen hW hg hξW)
  have hmul' : sumSquaresWithDriftTranspose C.Xl (fun y => a y * g (C.Θ η y)) ξ =
      a ξ * sumSquaresWithDriftTranspose C.Xl (g ∘ C.Θ η) ξ +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
          fieldDerivative (C.Xl i.succ) (g ∘ C.Θ η) ξ +
        (sumSquaresWithDriftTranspose C.Xl a ξ - a ξ * adjointCoeff C.Xl ξ) * g (C.Θ η ξ) := hmul
  have hs : ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
      fieldDerivative (C.Xl i.succ) a ξ) * C.zDeriv η i.succ g (C.Θ η ξ) =
      a ξ * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ *
        C.zDeriv η i.succ g (C.Θ η ξ) +
      ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ g (C.Θ η ξ) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hmul', hcr, hs]
  simp only [hz]
  ring

end LiftedChart

section TestFunctions

variable {n : ℕ}

/-- The derivative `V ψ` of a test function `ψ` on `Ω` along a field smooth on `Ω`
is a test function on `Ω`. -/
def fieldDerivativeTest (Ω : Opens (Fin n → ℝ)) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) := by
  have hz : ∀ x ∉ tsupport (ψ : (Fin n → ℝ) → ℝ), fieldDerivative V ψ x = 0 := fun x hx => by
    have : fderiv ℝ (ψ : (Fin n → ℝ) → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx ((tsupport_fderiv_subset ℝ) h))
    simp [fieldDerivative, this]
  refine ⟨fieldDerivative V ψ, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · exact (S.contDiffOn_fieldDerivative Ω V ψ hV ψ.contDiff.contDiffOn).contDiffAt
        (Ω.isOpen.mem_nhds hx)
    · have hxs : x ∉ tsupport (ψ : (Fin n → ℝ) → ℝ) := fun h => hx (ψ.tsupport_subset h)
      have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport (ψ : (Fin n → ℝ) → ℝ) :=
        isClosed_closure.isOpen_compl.mem_nhds hxs
      exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        (he.mono fun y hy => hz y hy)
  · exact HasCompactSupport.intro ψ.hasCompactSupport (fun x hx => hz x hx)
  · refine (closure_minimal (fun x hx => ?_) isClosed_closure).trans ψ.tsupport_subset
    by_contra h
    exact hx (hz x h)

theorem fieldDerivativeTest_apply (Ω : Opens (Fin n → ℝ)) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) (ψ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (x : Fin n → ℝ) : fieldDerivativeTest Ω V hV ψ x = fieldDerivative V ψ x := rfl

/-- `L̃ ψ = ∑ᵢ X̃ᵢ² ψ + X̃₀ ψ` of a test function is a test function. -/
def sumSquaresWithDriftTest {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  fieldDerivativeTest Ω (X 0) (hX 0) ψ +
    ∑ i : Fin q, fieldDerivativeTest Ω (X i.succ) (hX i.succ)
      (fieldDerivativeTest Ω (X i.succ) (hX i.succ) ψ)

theorem sumSquaresWithDriftTest_coe {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (sumSquaresWithDriftTest Ω X hX ψ : (Fin n → ℝ) → ℝ) = sumSquaresWithDrift X ψ := by
  funext x
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun φ => φ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h : (sumSquaresWithDriftTest Ω X hX ψ : (Fin n → ℝ) → ℝ) x =
      ev (fieldDerivativeTest Ω (X 0) (hX 0) ψ +
        ∑ i : Fin q, fieldDerivativeTest Ω (X i.succ) (hX i.succ)
          (fieldDerivativeTest Ω (X i.succ) (hX i.succ) ψ)) := rfl
  rw [h, map_add, map_sum]
  unfold sumSquaresWithDrift
  simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fieldDerivativeTest_apply]
  rfl

end TestFunctions

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

section Pullback

theorem isCompact_symm_image_tsupport {η : Fin (n + m) → ℝ}
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    IsCompact ((C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ)) :=
  g.hasCompactSupport.image_of_continuousOn ((C.e η).continuousOn_symm.mono g.tsupport_subset)

theorem symm_image_tsupport_subset {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := by
  rintro _ ⟨u, hu, rfl⟩
  have := (C.e η).map_target (g.tsupport_subset hu)
  rwa [e_source hη] at this

theorem comp_theta_eq_zero_of_notMem {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) {ξ : Fin (n + m) → ℝ} (hξU : ξ ∈ C.U)
    (hξ : ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ)) : g (C.Θ η ξ) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact hξ ⟨_, h, symm_theta hη hξU⟩

/-- The pullback `ξ ↦ a(ξ) g(Θ(η, ξ))` (extended by zero off `C.U`) of a test
function `g` of the model variable is a test function on the chart (its support lies in the compact
set `(e η)⁻¹ (supp g) ⊆ C.U`). -/
def pullbackTest {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := by
  have hKc := isCompact_symm_image_tsupport (C := C) g
  have hKU := symm_image_tsupport_subset hη g
  have hz : ∀ ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ),
      C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) ξ = 0 := fun ξ hξ => by
    by_cases hξU : ξ ∈ C.U
    · rw [indicator_of_mem hξU]
      simp [comp_theta_eq_zero_of_notMem hη g hξU hξ]
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
    · have hξK : ξ ∉ (C.e η).symm '' tsupport (g : (Fin (n + m) → ℝ) → ℝ) := fun h => hξU (hKU h)
      have hev : ∀ᶠ y in 𝓝 ξ, C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) y = 0 := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hξK] with y hy
        exact hz y hy
      exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin (n + m) → ℝ => (0 : ℝ)) ξ
        ).congr_of_eventuallyEq hev
  · exact HasCompactSupport.intro hKc hz
  · refine (closure_minimal (fun ξ hξ => ?_) hKc.isClosed).trans hKU
    by_contra h
    exact hξ (hz ξ h)

theorem pullbackTest_apply {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    pullbackTest hη ha g ξ = a ξ * g (C.Θ η ξ) := by
  show C.U.indicator (fun ξ => a ξ * g (C.Θ η ξ)) ξ = _
  exact indicator_of_mem hξ _

end Pullback

end LiftedChart

end RothschildStein.P1
