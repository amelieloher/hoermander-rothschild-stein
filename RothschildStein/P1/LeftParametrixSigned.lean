-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrix
public import RothschildStein.H1.KernelReflection

/-!
# The transposed left parametrix: `P₂ = P₁ᵗ`, `F₂ = F₁ᵗ` and `M_a = P₂ L̃ + F₂`

The transposed pair of the signed left parametrix (BB pp. 560–564, Thm 11.25, with the
sign erratum). With the H1 fundamental kernel `Γ` of the drift model, its reflection `Γ* = Γ ∘ inv`
(a fundamental kernel of the reversed-drift model; `inv = neg` on the chart group), cutoffs
`a, b ∈ C_c^∞(C.U)` with `a b = a`, put

`P₁ f(ξ) = a(ξ) ∫_U Γ*(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`,
`P₂ f(ξ) = (b(ξ) / c(ξ)) ∫_U a(η) Γ(Θ(η, ξ)) f(η) dη`   (`LiftedChart.leftParametrixT`),
`F₂ f(ξ) = -(b(ξ) / c(ξ)) ∫_U e*(ξ, η) f(η) dη`   (`LiftedChart.leftChartErrorT`),

`e*(ξ, η) = a(η) (E*_ξ Γ*)(Θ(ξ, η)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(η) (Zᵢ Γ*)(Θ(ξ, η)) +
(L̃* a)(η) Γ*(Θ(ξ, η))` (`leftErrBracket` with pole `ξ`).

* Kernel transposition (antisymmetry `Θ(ξ, η) = -Θ(η, ξ)` and `Γ*(u) = Γ(-u)`): the kernel of `P₂`
  is the transposed kernel of `P₁`, and that of `F₂` the transposed kernel of `F₁`; for tests,
  `∫ P₁ f · g = ∫ f · P₂ g` and `∫ F₁ f · g = ∫ f · F₂ g` (Fubini).
* The signed identity `M_a = P₂ L̃ + F₂` holds pointwise on the chart for tests `f`:
  `a(ξ) f(ξ) = P₂(L̃ f)(ξ) + F₂ f(ξ)` (the pole formula with the pole at `ξ` and the integration
  variable `η`), in particular `a u = P₂ L̃ u + F₂ u`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
open RothschildStein.P2
namespace RothschildStein.P1
namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The right-hand parametrix `P₂ f(ξ) = (b(ξ) / c(ξ)) ∫_U a(η) Γ(Θ(η, ξ))
f(η) dη` (BB pp. 560–564, Thm 11.25). -/
def leftParametrixT (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  b ξ / C.c ξ * ∫ η in C.U, a η * K (C.Θ η ξ) * f η

/-- The transposed error operator
`E₂ f(ξ) = (b(ξ) / c(ξ)) ∫_U e*(ξ, η) f(η) dη` (`e*` is `leftErrBracket` with pole `ξ`); its kernel
is the transpose of the kernel of `E₁`. -/
def leftErrorT (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  b ξ / C.c ξ * ∫ η in C.U, C.leftErrBracket K a ξ η * f η

/-- The transposed chart error `F₂ = -E₂ = F₁ᵗ` (in
`M_a = P₂ L̃ + F₂`; correcting the sign in BB pp. 560, 563). -/
def leftChartErrorT (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  -C.leftErrorT K a b f ξ

variable {C}

/-- Antisymmetry of `Θ` and `Γ*(u) = Γ(-u)`:
`Γ*(Θ(η, ξ)) = Γ(Θ(ξ, η))` for `η, ξ ∈ C.U` (BB Thm. 11.5(e)). -/
theorem reflection_theta {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (hξ : ξ ∈ C.U) : K.reflection hQ (C.Θ η ξ) = K (C.Θ ξ η) := by
  rw [K.reflection_neg hQ C.hasNegInverse, C.theta_antisymm η hη ξ hξ]

/-- The signed identity `M_a = P₂ L̃ + F₂` on tests (BB (11.39)–(11.40),
pp. 560–564, with the sign erratum): for the H1 fundamental kernel `Γ` of the
drift model, cutoffs `a, b` and a test `f` on `C.U` with `a b = a`, at every point `ξ` of the chart
`P₂(L̃ f)(ξ) + F₂ f(ξ) = a(ξ) f(ξ)`, that is `a f = P₂ L̃ f + F₂ f` (the pole formula
`integral_kernel_comp_theta_mul_sumSquares` with the pole at `ξ` and integration variable `η`). -/
theorem leftParametrixT_sumSquares_add_chartErrorT (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (a b f : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (hab : ∀ ξ, a ξ * b ξ = a ξ)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    C.leftParametrixT K a b (sumSquaresWithDrift C.Xl f) ξ +
      C.leftChartErrorT (K.reflection hQ) a b f ξ = a ξ * f ξ := by
  have haU : ContDiffOn ℝ (⊤ : ℕ∞) a C.U := a.contDiff.contDiffOn
  have hc : C.c ξ ≠ 0 := (C.density_pos ξ hξ).ne'
  have h := (integral_kernel_comp_theta_mul_sumSquares hq ν₀ (K.reflection hQ) hξ haU f).2
  have hrefl : (∫ η in C.U, a η * K (C.Θ η ξ) * sumSquaresWithDrift C.Xl f η) =
      ∫ η in C.U, a η * (K.reflection hQ) (C.Θ ξ η) * sumSquaresWithDrift C.Xl f η :=
    setIntegral_congr_fun C.isOpen_U.measurableSet (fun η hη => by
      rw [reflection_theta K hQ hξ hη])
  unfold leftParametrixT leftChartErrorT leftErrorT
  rw [hrefl, h]
  have e : b ξ / C.c ξ * (C.c ξ * (a ξ * f ξ)) = (a ξ * b ξ) * f ξ := by field_simp
  rw [mul_add, e, hab ξ]
  ring

/-- The signed identity `a u = P₂ L̃ u + F₂ u` for cutoffs `a, b ∈ C_c^∞(V)` and
a test `f ∈ C_c^∞(V)` supported in an open subset `V` of the chart domain. -/
theorem leftParametrixT_sumSquares_add_chartErrorT_of_le (V : Opens (Fin (n + m) → ℝ))
    (hV : V ≤ C.chartOpens) (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (a b f : TestFunction V ℝ (⊤ : ℕ∞)) (hab : ∀ ξ, a ξ * b ξ = a ξ)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    C.leftParametrixT K a b (sumSquaresWithDrift C.Xl f) ξ +
      C.leftChartErrorT (K.reflection hQ) a b f ξ = a ξ * f ξ :=
  leftParametrixT_sumSquares_add_chartErrorT hq ν₀ K hQ
    ⟨a, a.contDiff, a.hasCompactSupport, a.tsupport_subset.trans hV⟩
    ⟨b, b.contDiff, b.hasCompactSupport, b.tsupport_subset.trans hV⟩
    ⟨f, f.contDiff, f.hasCompactSupport, f.tsupport_subset.trans hV⟩ hab hξ

end LiftedChart

end RothschildStein.P1
