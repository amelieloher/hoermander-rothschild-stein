-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesOperators

/-!
# Parametrix error types: the error terms of one generator letter

For a generator letter `i` of a lifted chart (model field `Y i`, remainder `R_{[i],η}`, weight `w i`) and
the pole `P = F.pole star` of a frame `F`, with cutoffs `a, β, B ∈ C_c^∞(F.V)`:

* `isTypeKernelOn_horizontal_poleError`: for `w i = 1` the three second-order error terms
  `Yᵢ(Rᵢ P) + Rᵢ(Yᵢ P) + Rᵢ(Rᵢ P)` give a kernel of type `1` modeled on `star` (local degrees `≤ 1, 1, 0`,
  hence types `≥ 1, 1, 2`; BB pp. 561-563);
* `isTypeKernelOn_horizontal_zDeriv`: for `w i = 1` the first-order terms `Yᵢ P + Rᵢ P = Zᵢ P` give a kernel of
  type `1` (degrees `1` and `0`);
* `isTypeKernelOn_drift_remainder`: for `w i = 2` the drift remainder term `R_{[i],η} P` gives a kernel of type
  `1` (the drift letter has weight two, so `R₀` has local degree `1`).

All three are instances of the operator calculus of `ErrorTypesOperators` for the jet fields `Y i` (order
`-w i`) and `R_{[i],η}` (order `1 - w i`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1
namespace LiftedChart

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The three second-order error terms of a horizontal letter (`w i = 1`):
`a(ξ) β(η) (Yᵢ(Rᵢ P) + Rᵢ(Yᵢ P) + Rᵢ(Rᵢ P))(Θ(η, ξ))` is a kernel of type `1` modeled on `star`. -/
theorem isTypeKernelOn_horizontal_poleError (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (i : Fin k) (hw : ((w i : ℕ+) : ℕ) = 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a β : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star 1 (fun ξ η => a ξ * β η *
      (fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) (F.pole star)) (F.Θ η ξ) +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.Y i) (F.pole star)) (F.Θ η ξ) +
        fieldDerivative (C.R [i] η) (fieldDerivative (C.R [i] η) (F.pole star)) (F.Θ η ξ))) := by
  have hY : C.IsJetField (-((w i : ℕ) : ℤ)) (fun _ u => C.Y i u) := isJetField_Y i
  have hR : C.IsJetField (1 - ((w i : ℕ) : ℤ)) (fun η u => C.R [i] η u) := isJetField_R i
  have h1 := C.isTypeKernelOn_fieldDerivative_comp F hΘ hG hVU star 1 hY hR (by omega) hΓ hhom a β
  have h2 := C.isTypeKernelOn_fieldDerivative_comp F hΘ hG hVU star 1 hR hY (by omega) hΓ hhom a β
  have h3 := C.isTypeKernelOn_fieldDerivative_comp F hΘ hG hVU star 1 hR hR (by omega) hΓ hhom a β
  refine ((h1.add h2).add h3).congr_all fun ξ η => ?_
  ring

/-- The first-order terms `Zᵢ P = Yᵢ P + Rᵢ P` of a horizontal letter (`w i = 1`):
`B(ξ) β(η) (Yᵢ P + Rᵢ P)(Θ(η, ξ))` is a kernel of type `1` modeled on `star`. -/
theorem isTypeKernelOn_horizontal_zDeriv (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (i : Fin k) (hw : ((w i : ℕ+) : ℕ) = 1)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (B β : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star 1 (fun ξ η => B ξ * β η *
      (fieldDerivative (C.Y i) (F.pole star) (F.Θ η ξ) +
        fieldDerivative (C.R [i] η) (F.pole star) (F.Θ η ξ))) := by
  have hY : C.IsJetField (-((w i : ℕ) : ℤ)) (fun _ u => C.Y i u) := isJetField_Y i
  have hR : C.IsJetField (1 - ((w i : ℕ) : ℤ)) (fun η u => C.R [i] η u) := isJetField_R i
  have h1 := C.isTypeKernelOn_fieldDerivative F hΘ hG hVU star 1 hY (by omega) hΓ hhom B β
  have h2 := C.isTypeKernelOn_fieldDerivative F hΘ hG hVU star 1 hR (by omega) hΓ hhom B β
  refine (h1.add h2).congr_all fun ξ η => ?_
  ring

/-- The remainder term of a letter of weight at most two (the drift letter): `a(ξ) β(η)
(R_{[i],η} P)(Θ(η, ξ))` is a kernel of type `1` modeled on `star` (`R_{[i],η}` has order `1 - w i ≥ -1`). -/
theorem isTypeKernelOn_remainder_term (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (i : Fin k) (hw : ((w i : ℕ+) : ℕ) ≤ 2)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a β : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star 1 (fun ξ η => a ξ * β η *
      fieldDerivative (C.R [i] η) (F.pole star) (F.Θ η ξ)) := by
  have hR : C.IsJetField (1 - ((w i : ℕ) : ℤ)) (fun η u => C.R [i] η u) := isJetField_R i
  exact C.isTypeKernelOn_fieldDerivative F hΘ hG hVU star 1 hR (by omega) hΓ hhom a β

end LiftedChart

end RothschildStein.P1
