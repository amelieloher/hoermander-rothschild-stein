-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixPole
public import RothschildStein.P1.RightParametrixMass
public import RothschildStein.P1.RightParametrixFubini

/-!
# The signed right parametrix identity `L̃ P_R = M_a + E_R`, `F_R^chart = -E_R`

The right parametrix of the lifted drift chart (BB p. 605, Prop. 11.61, with the roles of Thm. 11.25
exchanged): for the H1 fundamental kernel `Γ` and cutoffs
`a, b ∈ C_c^∞(C.U)` with `a b = a`,

`P_R f(ξ) = a(ξ) ∫_U Γ(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`   (`LiftedChart.rightParametrix`),
`E_R f(ξ) = ∫_U e(ξ, η) f(η) dη`,
`e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) +
  (L̃ a)(ξ) Γ(Θ(η, ξ))]`   (`rightErrorKernel`, `rightError`).

For tests `f, φ` on `C.U`, `∫ P_R f · L̃ᵀφ = ∫ a f φ + ∫ (E_R f) φ`, that is
`L̃ P_R f = a f + E_R f` in the sense of distributions (`integral_rightParametrix_mul_transpose`),
and with `F_R^chart := -E_R`, `∫ P_R f · L̃ᵀφ = ∫ (a f - F_R^chart f) φ`
(`integral_rightParametrix_mul_transpose_chartError`). The proof
applies the pole limit `integral_kernel_comp_theta_mul_transpose` for each `η` and exchanges the
order of integration (Fubini) for the kernel and for the error kernel, whose lower integrals over
the support of the test are bounded uniformly in `η` (`RightParametrixMass`).
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

/-- The right parametrix `P_R f(ξ) = a(ξ) ∫_U Γ(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`
(BB p. 605, proof of Prop 11.61). -/
def rightParametrix (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * ∫ η in C.U, K (C.Θ η ξ) * (b η / C.c η * f η)

/-- The error kernel `e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ)(Θ(η, ξ)) +
2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))]` (the right pole computation). -/
def rightErrorKernel (K a b : (Fin (n + m) → ℝ) → ℝ) (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * C.errBracket K a η ξ

/-- The error operator `E_R f(ξ) = ∫_U e(ξ, η) f(η) dη`. -/
def rightError (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η in C.U, C.rightErrorKernel K a b ξ η * f η

/-- The chart error `F_R^chart = -E_R`, so that `L̃ P_R = M_a + E_R` reads
`M_a = L̃ P_R + F_R^chart`. -/
def rightChartError (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  -C.rightError K a b f ξ

variable {C}

end LiftedChart

end RothschildStein.P1
