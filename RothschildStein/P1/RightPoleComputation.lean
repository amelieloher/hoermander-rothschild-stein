-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightPoleComputationChain

/-!
# The direct computation of `L̃` on the right pole

Hold the input pole `η` fixed and apply `L̃` in the output variable `ξ` to `Γ(Θ(η, ξ))`
(the right pole computation; BB p. 605, Prop 11.61, with the roles of Thm 11.25 exchanged). For the drift
alphabet `Fin (q + 1)` (drift letter `0`), `L̃ = ∑_{i ≥ 1} X̃ᵢ² + X̃₀` is
`sumSquaresWithDrift C.Xl` and `𝓛 = ∑_{i ≥ 1} Yᵢ² + Y₀` is `sumSquaresWithDrift C.Y`. With
`Rᵢ = R_{[i],η}`, for `ξ ∈ C.U` and `Γ` smooth on an open set containing `Θ η ξ`

`L̃_ξ[Γ(Θ(η, ξ))] = (𝓛 Γ)(Θ(η, ξ)) + E(η, Θ(η, ξ))`,
`E = ∑_{i ≥ 1} (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ + R₀ Γ`,

the drift remainder entering with the **positive** sign (`sumSquaresWithDrift_comp_theta`). The
weights `w` play no role in this algebraic identity; the lifted chart's `w 0 = 2` enters only
through `LiftedChart.driftModel` (the standing hypotheses of H1). For `Γ` smooth off the origin
and `ξ ≠ η` one has `Θ η ξ ≠ 0`; if moreover `𝓛 Γ = 0` off the origin (the H1 property of the
fundamental kernel) then `L̃_ξ[Γ(Θ(η, ξ))] = E(η, Θ(η, ξ))` for `ξ ≠ η`.

The output product formula (`sumSquaresWithDrift_mul_comp_theta`) is
`L̃(a g) = a L̃g + 2 ∑ᵢ (X̃ᵢ a)(X̃ᵢ g) + (L̃ a) g` for `g = Γ ∘ Θ η`, with `X̃ᵢ g = (Zᵢ Γ) ∘ Θ η`.
The no-drift forms (alphabet `Fin q`, `sumSquares`) are the same statements without the
letter `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1
namespace LiftedChart

section Smoothness

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The lifted fields are smooth on the lifted neighborhood
`C.U` (`LiftedChart.lift_smooth` and `closure U ⊆ O`). -/
theorem contDiffOn_Xl_U (i : Fin k) : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) C.U :=
  (C.lift_smooth i).mono (subset_closure.trans C.closure_U_subset)

/-- The set of `ξ ∈ C.U` with `Θ η ξ` in an open set `W` is
open. -/
theorem isOpen_theta_preimage {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) : IsOpen (C.U ∩ C.Θ η ⁻¹' W) :=
  (C.contDiffOn_theta hη).continuousOn.isOpen_inter_preimage C.isOpen_U hW

/-- `Γ ∘ Θ η` is smooth on the open set of `ξ ∈ C.U` with
`Θ η ξ ∈ W` when `Γ` is smooth on `W`. -/
theorem contDiffOn_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ W) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Γ ∘ C.Θ η) (C.U ∩ C.Θ η ⁻¹' W) :=
  hΓ.comp ((C.contDiffOn_theta hη).mono inter_subset_left) (fun _ h => h.2)

end Smoothness

section Drift

variable {n q s m : ℕ} {w : Fin (q + 1) → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The error `E(η, u)` of the right pole formula, before the output cutoff:
`E = ∑_{i ≥ 1} (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ + R₀ Γ` with `Rᵢ = R_{[i],η}`; the drift remainder `R₀`
enters with the positive sign. -/
def rightPoleError (η : Fin (n + m) → ℝ) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) Γ) u +
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (C.Y i.succ) Γ) u +
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (C.R [i.succ] η) Γ) u) +
    fieldDerivative (C.R [0] η) Γ u

/-- The right pole formula (BB p. 605):
for `η, ξ ∈ C.U` and `Γ` smooth on an open set `W ∋ Θ η ξ`,
`L̃_ξ[Γ(Θ(η, ξ))] = (𝓛 Γ)(Θ(η, ξ)) + E(η, Θ(η, ξ))`, where `L̃ = ∑_{i ≥ 1} X̃ᵢ² + X̃₀`,
`𝓛 = ∑_{i ≥ 1} Yᵢ² + Y₀`, and the drift remainder has the positive sign. -/
theorem sumSquaresWithDrift_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresWithDrift C.Xl (Γ ∘ C.Θ η) ξ =
      sumSquaresWithDrift C.Y Γ (C.Θ η ξ) + C.rightPoleError η Γ (C.Θ η ξ) := by
  have h0 := C.fieldDerivative_comp_theta hη 0 hξ
    (differentiableAt_of_contDiffOn_isOpen hW hΓ hξW)
  have hi := fun i : Fin q =>
    C.fieldDerivative_fieldDerivative_comp_theta_expand hη i.succ hW hΓ hξ hξW
  simp only [sumSquaresWithDrift, rightPoleError, h0, hi, zDeriv, Finset.sum_add_distrib]
  ring

/-- The output product formula for the right pole:
for `a` smooth on `C.U`, `η, ξ ∈ C.U` and `Γ` smooth on an open `W ∋ Θ η ξ`,
`L̃_ξ[a Γ(Θ(η, ξ))] = a(ξ) ((𝓛Γ)(Θ(η, ξ)) + E(η, Θ(η, ξ)))
  + 2 ∑_{i ≥ 1} (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`,
`Zᵢ = Yᵢ + R_{[i],η}` (so `X̃ᵢ[Γ ∘ Θ η] = (Zᵢ Γ) ∘ Θ η`); there are no adjoint-divergence
corrections because the output operator is `L̃` itself. -/
theorem sumSquaresWithDrift_mul_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ W) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquaresWithDrift C.Xl (fun ξ' => a ξ' * Γ (C.Θ η ξ')) ξ =
      a ξ * (sumSquaresWithDrift C.Y Γ (C.Θ η ξ) + C.rightPoleError η Γ (C.Θ η ξ)) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ Γ (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * Γ (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hg := C.contDiffOn_comp_theta hη hΓ
  have hmul : sumSquaresWithDrift C.Xl (fun y => a y * (Γ ∘ C.Θ η) y) ξ =
      a ξ * sumSquaresWithDrift C.Xl (Γ ∘ C.Θ η) ξ +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
          fieldDerivative (C.Xl i.succ) (Γ ∘ C.Θ η) ξ +
        sumSquaresWithDrift C.Xl a ξ * (Γ ∘ C.Θ η) ξ :=
    sumSquaresWithDrift_mul hO (fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left)
      (ha.mono inter_subset_left) hg hξO
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i.succ hξ
    (differentiableAt_of_contDiffOn_isOpen hW hΓ hξW)
  rw [← C.sumSquaresWithDrift_comp_theta hη hW hΓ hξ hξW]
  simp only [hz] at hmul
  exact hmul

end Drift

section NoDrift

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The no-drift error of the right pole formula:
`E = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ Rᵢ) Γ`, `Rᵢ = R_{[i],η}`. -/
def rightPoleErrorNoDrift (η : Fin (n + m) → ℝ) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) Γ) u +
    fieldDerivative (C.R [i] η) (fieldDerivative (C.Y i) Γ) u +
    fieldDerivative (C.R [i] η) (fieldDerivative (C.R [i] η) Γ) u)

/-- The no-drift form of the right pole formula: for `η, ξ ∈ C.U` and `Γ`
smooth on an open `W ∋ Θ η ξ`, `L̃_ξ[Γ(Θ(η, ξ))] = (𝓛 Γ)(Θ(η, ξ)) + E(η, Θ(η, ξ))` with
`L̃ = ∑ᵢ X̃ᵢ²`, `𝓛 = ∑ᵢ Yᵢ²`. -/
theorem sumSquares_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ W) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquares C.Xl (Γ ∘ C.Θ η) ξ =
      sumSquares C.Y Γ (C.Θ η ξ) + C.rightPoleErrorNoDrift η Γ (C.Θ η ξ) := by
  have hi := fun i : Fin q =>
    C.fieldDerivative_fieldDerivative_comp_theta_expand hη i hW hΓ hξ hξW
  simp only [sumSquares, rightPoleErrorNoDrift, hi, Finset.sum_add_distrib]
  ring

/-- The no-drift output product formula for the right pole:
`L̃_ξ[a Γ(Θ(η, ξ))] = a(ξ) ((𝓛Γ)(Θ(η, ξ)) + E(η, Θ(η, ξ)))
  + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))`. -/
theorem sumSquares_mul_comp_theta {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {Γ : (Fin (n + m) → ℝ) → ℝ}
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ W) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hξW : C.Θ η ξ ∈ W) :
    sumSquares C.Xl (fun ξ' => a ξ' * Γ (C.Θ η ξ')) ξ =
      a ξ * (sumSquares C.Y Γ (C.Θ η ξ) + C.rightPoleErrorNoDrift η Γ (C.Θ η ξ)) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i) a ξ * C.zDeriv η i Γ (C.Θ η ξ) +
        sumSquares C.Xl a ξ * Γ (C.Θ η ξ) := by
  have hO := C.isOpen_theta_preimage hη hW
  have hξO : ξ ∈ C.U ∩ C.Θ η ⁻¹' W := ⟨hξ, hξW⟩
  have hg := C.contDiffOn_comp_theta hη hΓ
  have hmul : sumSquares C.Xl (fun y => a y * (Γ ∘ C.Θ η) y) ξ =
      a ξ * sumSquares C.Xl (Γ ∘ C.Θ η) ξ +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i) a ξ *
          fieldDerivative (C.Xl i) (Γ ∘ C.Θ η) ξ +
        sumSquares C.Xl a ξ * (Γ ∘ C.Θ η) ξ :=
    sumSquares_mul hO (fun i => (C.contDiffOn_Xl_U i).mono inter_subset_left)
      (ha.mono inter_subset_left) hg hξO
  have hz := fun i : Fin q => C.fieldDerivative_comp_theta hη i hξ
    (differentiableAt_of_contDiffOn_isOpen hW hΓ hξW)
  rw [← C.sumSquares_comp_theta hη hW hΓ hξ hξW]
  simp only [hz] at hmul
  exact hmul

end NoDrift

end LiftedChart

end RothschildStein.P1
