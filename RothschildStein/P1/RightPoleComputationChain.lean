-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.Definitions.fieldDerivative
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.H1.OperatorAlgebra
public import RothschildStein.S.Transposes

/-!
# The chain rule for the lifted fields and the output product formula

Calculus behind the right pole formula, the direct computation of `L̃` applied to `Γ(Θ(η, ξ))` in the output
variable `ξ` (the right pole computation; BB p. 605, Prop 11.61, with the roles of Thm 11.25 exchanged).

* `LiftedChart.fieldDerivative_comp_theta`: for `η ∈ C.U`, a letter `i`, and `h` differentiable at
  `Θ η ξ`, `X̃ᵢ[h ∘ Θ η] (ξ) = (Yᵢ h + R_{[i],η} h) (Θ η ξ)` (the field `Zᵢ = Yᵢ + R_{[i],η}` of
  `LiftedChart.bracket_approx` with `I = [i]`).
* `LiftedChart.fieldDerivative_fieldDerivative_comp_theta_expand`: for `h` smooth on an open set
  `W` containing `Θ η ξ`, `X̃ᵢ X̃ᵢ [h ∘ Θ η] (ξ) = ((YᵢYᵢ + YᵢRᵢ + RᵢYᵢ + RᵢRᵢ) h) (Θ η ξ)`
  (`LiftedChart.remainder_smooth` gives smoothness of `R_{[i],η}` on `(e η).target`).
* `sumSquaresWithDrift_mul`, `sumSquares_mul`: `L̃(a g) = a L̃g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃ a) g`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1

section Product

variable {n : ℕ}

/-- Smoothness on an open set gives differentiability at each of
its points (calculus used for the chain rule and the output product formula). -/
theorem differentiableAt_of_contDiffOn_isOpen {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {W : Set E} (hW : IsOpen W)
    {f : E → F} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W) {x : E} (hx : x ∈ W) :
    DifferentiableAt ℝ f x :=
  (hf.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)

/-- Field differentiation of a sum of two differentiable
functions. -/
theorem fieldDerivative_fun_add_apply {V : (Fin n → ℝ) → (Fin n → ℝ)}
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (fun y => f y + g y) x = fieldDerivative V f x + fieldDerivative V g x :=
  H1.fieldDerivative_add_at V hf hg

/-- The square of one smooth field acting on a product of smooth
functions on an open set: `V²(a g) = (V²a) g + 2 (Va)(Vg) + a (V²g)` (output product formula, one
field). -/
theorem fieldDerivative_square_mul_pointwise {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    {V : (Fin n → ℝ) → (Fin n → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V W)
    {a g : (Fin n → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a W)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {x : Fin n → ℝ} (hx : x ∈ W) :
    fieldDerivative V (fieldDerivative V (fun y => a y * g y)) x =
      fieldDerivative V (fieldDerivative V a) x * g x +
        2 * (fieldDerivative V a x * fieldDerivative V g x) +
        a x * fieldDerivative V (fieldDerivative V g) x := by
  let Wo : Opens (Fin n → ℝ) := ⟨W, hW⟩
  have hVa : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative V a) W :=
    S.contDiffOn_fieldDerivative Wo V a hV ha
  have hVg : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative V g) W :=
    S.contDiffOn_fieldDerivative Wo V g hV hg
  have hd : ∀ {F : (Fin n → ℝ) → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) F W → ∀ {y : Fin n → ℝ},
      y ∈ W → DifferentiableAt ℝ F y :=
    fun hF _ hy => differentiableAt_of_contDiffOn_isOpen hW hF hy
  have heq : fieldDerivative V (fun y => a y * g y) =ᶠ[𝓝 x]
      fun y => fieldDerivative V a y * g y + a y * fieldDerivative V g y := by
    filter_upwards [hW.mem_nhds hx] with y hy
    rw [S.fieldDerivative_mul V a g y (hd ha hy) (hd hg hy)]
  have h1 : fieldDerivative V (fieldDerivative V (fun y => a y * g y)) x =
      fieldDerivative V
        (fun y => fieldDerivative V a y * g y + a y * fieldDerivative V g y) x := by
    show fderiv ℝ (fieldDerivative V (fun y => a y * g y)) x (V x) = _
    rw [heq.fderiv_eq]
    rfl
  rw [h1, fieldDerivative_fun_add_apply ((hd hVa hx).fun_mul (hd hg hx))
    ((hd ha hx).fun_mul (hd hVg hx)),
    S.fieldDerivative_mul V (fieldDerivative V a) g x (hd hVa hx) (hd hg hx),
    S.fieldDerivative_mul V a (fieldDerivative V g) x (hd ha hx) (hd hVg hx)]
  ring

/-- Output product formula for the drift operator
`L̃ = X̃₀ + ∑ᵢ X̃ᵢ²` (drift letter `0`, horizontal letters `i.succ`):
`L̃(a g) = a L̃g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃ a) g` for `a, g, X̃ᵢ` smooth on an open set
(the right pole computation; no adjoint-divergence corrections). -/
theorem sumSquaresWithDrift_mul {q : ℕ} {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) W)
    {a g : (Fin n → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a W)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {x : Fin n → ℝ} (hx : x ∈ W) :
    sumSquaresWithDrift X (fun y => a y * g y) x =
      a x * sumSquaresWithDrift X g x +
        2 * ∑ i : Fin q, fieldDerivative (X i.succ) a x * fieldDerivative (X i.succ) g x +
        sumSquaresWithDrift X a x * g x := by
  have h0 := S.fieldDerivative_mul (X 0) a g x (differentiableAt_of_contDiffOn_isOpen hW ha hx)
    (differentiableAt_of_contDiffOn_isOpen hW hg hx)
  have hi := fun i : Fin q => fieldDerivative_square_mul_pointwise hW (hX i.succ) ha hg hx
  simp only [sumSquaresWithDrift, h0, hi, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

/-- The no-drift output product formula for `L̃ = ∑ᵢ X̃ᵢ²`:
`L̃(a g) = a L̃g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃ a) g`. -/
theorem sumSquares_mul {q : ℕ} {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) W)
    {a g : (Fin n → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a W)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {x : Fin n → ℝ} (hx : x ∈ W) :
    sumSquares X (fun y => a y * g y) x =
      a x * sumSquares X g x +
        2 * ∑ i : Fin q, fieldDerivative (X i) a x * fieldDerivative (X i) g x +
        sumSquares X a x * g x := by
  have hi := fun i : Fin q => fieldDerivative_square_mul_pointwise hW (hX i) ha hg hx
  simp only [sumSquares, hi, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

end Product

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- For `η ∈ C.U` the two-point map `ξ ↦ Θ η ξ` is smooth on
`C.U` (`LiftedChart.chart`: it is the endpoint chart `e η` there). -/
theorem contDiffOn_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Θ η) C.U := by
  obtain ⟨hsrc, heq, hcd, -, -⟩ := C.chart η hη
  rw [hsrc] at hcd
  exact hcd.congr fun ξ hξ => (heq ξ hξ).symm

/-- `ξ ↦ Θ η ξ` is differentiable at every `ξ ∈ C.U`. -/
theorem differentiableAt_theta {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    DifferentiableAt ℝ (C.Θ η) ξ :=
  differentiableAt_of_contDiffOn_isOpen C.isOpen_U (C.contDiffOn_theta hη) hξ

/-- `Θ η ξ` lies in the target of the endpoint chart `e η`
for `ξ ∈ C.U`. -/
theorem theta_mem_target {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    C.Θ η ξ ∈ (C.e η).target := by
  obtain ⟨hsrc, heq, -, -, -⟩ := C.chart η hη
  rw [← heq ξ hξ]
  exact (C.e η).map_source (by rw [hsrc]; exact hξ)

/-- `Θ η ξ ≠ 0` for `ξ ∈ C.U`, `ξ ≠ η` (the endpoint chart is
injective and `Θ η η = 0`). -/
theorem theta_ne_zero {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) (hne : ξ ≠ η) :
    C.Θ η ξ ≠ 0 := by
  obtain ⟨hsrc, heq, -, -, h0⟩ := C.chart η hη
  intro hz
  apply hne
  have h1 : (C.e η) ξ = (C.e η) η := by rw [heq ξ hξ, heq η hη, hz, h0]
  exact (C.e η).injOn (by rw [hsrc]; exact hξ) (by rw [hsrc]; exact hη) h1

/-- For `η ∈ C.U` and every word `I`, the remainder
`u ↦ R I η u` is smooth on the target of the endpoint chart `e η` (slice of
`LiftedChart.remainder_smooth`). -/
theorem contDiffOn_remainder {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (I : List (Fin k)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η) (C.e η).target := by
  have hmap : MapsTo (fun u : Fin (n + m) → ℝ => (η, u)) (C.e η).target C.T :=
    fun u hu => ⟨hη, hu⟩
  exact (C.remainder_smooth I).comp (contDiff_const.prodMk contDiff_id).contDiffOn hmap

/-- The output-variable operator `Zᵢ = Yᵢ + R_{[i],η}` of the
lifted chain rule, acting on functions of the model variable `u`:
`Zᵢ h = Yᵢ h + R_{[i],η} h` (`LiftedChart.bracket_approx` with `I = [i]`). -/
def zDeriv (η : Fin (n + m) → ℝ) (i : Fin k) (h : (Fin (n + m) → ℝ) → ℝ) :
    (Fin (n + m) → ℝ) → ℝ :=
  fun u => fieldDerivative (C.Y i) h u + fieldDerivative (C.R [i] η) h u

/-- Lifted chain rule, first order: for `η ∈ C.U`, a letter `i`,
`ξ ∈ C.U` and `h` differentiable at `Θ η ξ`,
`X̃ᵢ[h ∘ Θ η] (ξ) = (Zᵢ h) (Θ η ξ)` with `Zᵢ = Yᵢ + R_{[i],η}`. -/
theorem fieldDerivative_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin k)
    {h : (Fin (n + m) → ℝ) → ℝ} {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hh : DifferentiableAt ℝ h (C.Θ η ξ)) :
    fieldDerivative (C.Xl i) (h ∘ C.Θ η) ξ = C.zDeriv η i h (C.Θ η ξ) := by
  have hb : fderiv ℝ (C.Θ η) ξ (C.Xl i ξ) = C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ) :=
    C.bracket_approx [i] (List.cons_ne_nil _ _) η hη ξ hξ
  unfold fieldDerivative zDeriv
  rw [fderiv_comp ξ hh (C.differentiableAt_theta hη hξ), ContinuousLinearMap.comp_apply, hb,
    map_add]
  rfl

/-- `Zᵢ h` is differentiable at `u` when `h` is smooth on an open
set `W ∋ u` and `u` is in the target of `e η` (`Yᵢ` is smooth; `R_{[i],η}` is smooth there). -/
theorem differentiableAt_zDeriv {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin k)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {h : (Fin (n + m) → ℝ) → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h W) {u : Fin (n + m) → ℝ} (huW : u ∈ W)
    (hut : u ∈ (C.e η).target) : DifferentiableAt ℝ (C.zDeriv η i h) u := by
  have h2 : ContDiffAt ℝ 2 h u :=
    (hh.contDiffAt (hW.mem_nhds huW)).of_le (by simp)
  have hY : DifferentiableAt ℝ (C.Y i) u :=
    ((C.model_field_smooth i).differentiable (by simp)).differentiableAt
  have hR : DifferentiableAt ℝ (C.R [i] η) u :=
    differentiableAt_of_contDiffOn_isOpen (C.e η).open_target (C.contDiffOn_remainder hη [i]) hut
  exact (H1.differentiableAt_fieldDerivative h2 hY).add
    (H1.differentiableAt_fieldDerivative h2 hR)

/-- Lifted chain rule, second order: for `η ∈ C.U`, `ξ ∈ C.U` and
`h` smooth on an open set `W ∋ Θ η ξ`, `X̃ᵢ X̃ᵢ [h ∘ Θ η] (ξ) = (Zᵢ Zᵢ h) (Θ η ξ)`. -/
theorem fieldDerivative_fieldDerivative_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (i : Fin k) {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {h : (Fin (n + m) → ℝ) → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) (h ∘ C.Θ η)) ξ =
      C.zDeriv η i (C.zDeriv η i h) (C.Θ η ξ) := by
  have hcont : ContinuousAt (C.Θ η) ξ := (C.differentiableAt_theta hη hξ).continuousAt
  have heq : fieldDerivative (C.Xl i) (h ∘ C.Θ η) =ᶠ[𝓝 ξ] (C.zDeriv η i h ∘ C.Θ η) := by
    filter_upwards [C.isOpen_U.mem_nhds hξ, hcont.preimage_mem_nhds (hW.mem_nhds hξW)]
      with ξ' h1 h2
    exact C.fieldDerivative_comp_theta hη i h1 (differentiableAt_of_contDiffOn_isOpen hW hh h2)
  have hzd := C.differentiableAt_zDeriv hη i hW hh hξW (C.theta_mem_target hη hξ)
  show fderiv ℝ (fieldDerivative (C.Xl i) (h ∘ C.Θ η)) ξ (C.Xl i ξ) = _
  rw [heq.fderiv_eq]
  exact C.fieldDerivative_comp_theta hη i hξ hzd

/-- Expansion of `Zᵢ Zᵢ`:
`Zᵢ Zᵢ h = YᵢYᵢ h + Yᵢ(Rᵢ h) + Rᵢ(Yᵢ h) + RᵢRᵢ h` with `Rᵢ = R_{[i],η}`, for `h` smooth on an
open `W ∋ u` and `u` in the target of `e η`. -/
theorem zDeriv_zDeriv_apply {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin k)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {h : (Fin (n + m) → ℝ) → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h W) {u : Fin (n + m) → ℝ} (huW : u ∈ W)
    (hut : u ∈ (C.e η).target) :
    C.zDeriv η i (C.zDeriv η i h) u =
      fieldDerivative (C.Y i) (fieldDerivative (C.Y i) h) u +
        fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) h) u +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.Y i) h) u +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.R [i] η) h) u := by
  have h2 : ContDiffAt ℝ 2 h u :=
    (hh.contDiffAt (hW.mem_nhds huW)).of_le (by simp)
  have hY : DifferentiableAt ℝ (C.Y i) u :=
    ((C.model_field_smooth i).differentiable (by simp)).differentiableAt
  have hR : DifferentiableAt ℝ (C.R [i] η) u :=
    differentiableAt_of_contDiffOn_isOpen (C.e η).open_target (C.contDiffOn_remainder hη [i]) hut
  have hA := H1.differentiableAt_fieldDerivative h2 hY
  have hB := H1.differentiableAt_fieldDerivative h2 hR
  have e1 : ∀ V : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
      fieldDerivative V (C.zDeriv η i h) u =
        fieldDerivative V (fieldDerivative (C.Y i) h) u +
          fieldDerivative V (fieldDerivative (C.R [i] η) h) u :=
    fun V => fieldDerivative_fun_add_apply hA hB
  change fieldDerivative (C.Y i) (C.zDeriv η i h) u + fieldDerivative (C.R [i] η) (C.zDeriv η i h) u
    = _
  rw [e1, e1]
  ring

/-- Lifted chain rule, second order, expanded: for `η, ξ ∈ C.U`
and `h` smooth on an open `W ∋ Θ η ξ`,
`X̃ᵢ X̃ᵢ [h ∘ Θ η] (ξ) = ((YᵢYᵢ + YᵢRᵢ + RᵢYᵢ + RᵢRᵢ) h) (Θ η ξ)`, `Rᵢ = R_{[i],η}`. -/
theorem fieldDerivative_fieldDerivative_comp_theta_expand {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (i : Fin k) {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {h : (Fin (n + m) → ℝ) → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    fieldDerivative (C.Xl i) (fieldDerivative (C.Xl i) (h ∘ C.Θ η)) ξ =
      fieldDerivative (C.Y i) (fieldDerivative (C.Y i) h) (C.Θ η ξ) +
        fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) h) (C.Θ η ξ) +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.Y i) h) (C.Θ η ξ) +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.R [i] η) h) (C.Θ η ξ) := by
  rw [C.fieldDerivative_fieldDerivative_comp_theta hη i hW hh hξ hξW]
  exact C.zDeriv_zDeriv_apply hη i hW hh hξW (C.theta_mem_target hη hξ)

end LiftedChart

end RothschildStein.P1
