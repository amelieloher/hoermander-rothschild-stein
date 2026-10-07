-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixSigned
public import RothschildStein.P1.TypeCalculusStatements
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresWithDrift

/-!
# Signed parametrix identities at operator level

`SignedParametrix F Xt c a b` gives the operator-level conclusion of the signed parametrix (BB
pp. 560–564, Thm 11.25, (11.39)–(11.40)) for a kernel frame `F` (poles `F.Γ`, `F.Γs`, two-point
map `F.Θ`), lifted fields `Xt` of a drift alphabet (`L̃ = sumSquaresWithDrift Xt`), density `c`, and
cutoffs `a, b ∈ C_c^∞(V)` with `a b = a`: there are

* `P₁, P₂` of type 2 with the explicit kernels `a(ξ) Γ*(Θ(η, ξ)) b(η) / c(η)` and
  `(b/c)(ξ) a(η) Γ(Θ(η, ξ))` (off the diagonal), `P₂ = P₁ᵗ`;
* `F₁, F₂` of type 1, `F₁` modeled on `Γ*` and `F₂` on `Γ` (every principal term of every
  decomposition has that pole), `F₂ = F₁ᵗ`;
* `M_a = L̃* P₁ + F₁` in the sense of distributions on tests (`∫ P₁ f · L̃ φ = ∫ a f φ - ∫ F₁ f · φ`,
  the pairings being integrable) and `M_a = P₂ L̃ + F₂` (`a f = P₂ (L̃ f) + F₂ f` on `V`).

The density `c` enters through `b / c ∈ C_c^∞(V)`, so smoothness of `c` on `V` and positivity are
the standing hypotheses of the statement (`C.density_smooth`, `C.density_pos` of a lifted chart).
`SignedParametrixNoDrift` is the same statement for the no-drift alphabet (`L̃ = sumSquares Xt`).

`ParametrixErrorTypes` is the type bound for the explicit error kernel of the left
parametrix of the lifted chart (`LiftedChart.leftErrorKernel`, `F₁ = -E₁`): the kernel of `F₁` is a
type-1 kernel modeled on `Γ*` for the frame and its transpose (the kernel of `F₂`) is type 1 modeled
on `Γ` (BB pp. 561–563: the error terms have local degrees at most `1, 1, 0, 1`, hence types at
least `1, 1, 2, 1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

variable {N : ℕ}

/-- `k` is a type-`lam` kernel *modeled on* the pole `Γ` (`star = false`) or `Γ*`
(`star = true`): for every regularity budget there is a decomposition into principal terms and a regular remainder all of whose principal
terms have that pole (BB p. 543, Def 11.7). -/
def IsTypeKernelOn (F : KernelFrame N) (star : Bool) (lam : ℕ)
    (k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ m : ℕ, ∃ d : TypeDecomposition F lam m k, ∀ t ∈ d.principal, t.star = star

/-- A kernel of type `lam` modeled on a pole has type `lam`. -/
theorem IsTypeKernelOn.isTypeKernel {F : KernelFrame N} {star : Bool} {lam : ℕ}
    {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h : IsTypeKernelOn F star lam k) :
    IsTypeKernel F lam k := fun m => (h m).elim fun d _ => ⟨d⟩

/-- The operator-level conclusion of the signed parametrix, `M_a = L̃* P₁ + F₁` and
`M_a = P₂ L̃ + F₂`, for a kernel
frame `F`, an operator `Lt` standing for `L̃`, the density `c` and cutoffs `a, b ∈ C_c^∞(V)` with
`a b = a` (BB pp. 560–564, Thm 11.25, with the sign erratum): type-2 `P₁, P₂` with kernels
`a(ξ) Γ*(Θ(η, ξ)) b(η) / c(η)` and `(b/c)(ξ) a(η) Γ(Θ(η, ξ))` (off the diagonal), `P₂ = P₁ᵗ`,
type-1 `F₁, F₂` modeled on `Γ*`, `Γ` with `F₂ = F₁ᵗ`, and `M_a = L̃* P₁ + F₁`,
`M_a = P₂ L̃ + F₂` on tests. Smoothness and positivity of `c` on `V` are the standing hypotheses
under which `b / c ∈ C_c^∞(V)`. -/
def SignedParametrixOf (F : KernelFrame N) (Lt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (c : (Fin N → ℝ) → ℝ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)) → (∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) →
  (∀ ξ, a ξ * b ξ = a ξ) →
    ∃ (P₁ P₂ : TypeOperator F 2) (F₁ F₂ : TypeOperator F 1),
      (∀ ξ η, ξ ≠ η → P₁.kernel ξ η = a ξ * F.Γs (F.Θ η ξ) * (b η / c η)) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = b ξ / c ξ * (a η * F.Γ (F.Θ η ξ))) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = P₁.kernel η ξ) ∧
      (∀ ξ η, ξ ≠ η → F₂.kernel ξ η = F₁.kernel η ξ) ∧
      IsTypeKernelOn F true 1 F₁.kernel ∧ IsTypeKernelOn F false 1 F₂.kernel ∧
      (∀ f φ : TestFunction F.V ℝ (⊤ : ℕ∞),
        IntegrableOn (fun ξ => P₁.apply f ξ * Lt φ ξ) (F.V : Set (Fin N → ℝ)) ∧
        IntegrableOn (fun ξ => F₁.apply f ξ * φ ξ) (F.V : Set (Fin N → ℝ)) ∧
        (∫ ξ in (F.V : Set (Fin N → ℝ)), P₁.apply f ξ * Lt φ ξ) =
          (∫ ξ in (F.V : Set (Fin N → ℝ)), a ξ * f ξ * φ ξ) -
            ∫ ξ in (F.V : Set (Fin N → ℝ)), F₁.apply f ξ * φ ξ) ∧
      (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin N → ℝ)),
        a ξ * f ξ = P₂.apply (Lt f) ξ + F₂.apply f ξ)

/-- The operator-level conclusion of the signed parametrix for the lifted fields `Xt` of a drift alphabet
(`L̃ = sumSquaresWithDrift Xt`, drift at index `0`), the density `c` and cutoffs `a, b` with
`a b = a`. -/
def SignedParametrix {q : ℕ} (F : KernelFrame N) (Xt : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop :=
  SignedParametrixOf F (sumSquaresWithDrift Xt) c a b

/-- The operator-level conclusion of the signed parametrix without drift (`L̃ = ∑ᵢ X̃ᵢ²`, the no-drift
lifted alphabet of weights one). -/
def SignedParametrixNoDrift {q : ℕ} (F : KernelFrame N) (Xt : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop :=
  SignedParametrixOf F (sumSquares Xt) c a b

section ErrorTypes

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The types of the error terms: for the H1 fundamental kernel `Γ` of the drift
model of a lifted chart `C`, its reflection `Γ* = Γ ∘ inv`, cutoffs `a, b ∈ C_c^∞(V)` with
`a b = a`, the explicit error kernel of `F₁ = -E₁` (`LiftedChart.leftErrorKernel`, so that
`leftChartError = -leftError`) is a type-1 kernel modeled on `Γ*` for the frame `F`, and its
transpose, the kernel of `F₂ = F₁ᵗ`, is a type-1 kernel modeled on `Γ` (BB pp. 561–563,
the pole computation: local degrees at most `1, 1, 0, 1`, hence types at least `1, 1, 2, 1`;
divergence and cross-cutoff terms have type 1). -/
def ParametrixErrorTypes
    (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)
    (F : KernelFrame (n + m)) (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (Γ : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop :=
  (∀ ξ, a ξ * b ξ = a ξ) →
    IsTypeKernelOn F true 1 (fun ξ η => -C.leftErrorKernel (Γ.reflection hQ) a b ξ η) ∧
    IsTypeKernelOn F false 1 (fun ξ η => -C.leftErrorKernel (Γ.reflection hQ) a b η ξ)

end ErrorTypes

end RothschildStein.P1
