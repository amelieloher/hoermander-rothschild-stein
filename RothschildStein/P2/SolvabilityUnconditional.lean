-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilitySolution
public import RothschildStein.P1.RightParametrixLp

/-!
# Local solvability: the `L^p` identity extension and the solutions `L̃ P_R E_r f = g`

`rightLpIdentity` proves `RightLpIdentity K a b p`: for every `u ∈ L^p(V)` and every
test `φ` of `V`, `∫_V P_R u · L̃ᵀφ = ∫_V (a u - F_R^chart u) φ`
test `φ` of `V = C.U`, is **proved** here under the standing cutoff relation `a b = a`, for every
exponent `1 ≤ p ≤ ∞` (`rightLpIdentity`). The proof is the identity on tests
(`integral_rightParametrix_mul_transpose_chartError`) run for a locally integrable input: an
`L^p(V)` function is integrable on the compact support of `b` (`locallyIntegrableOn_of_memLp`),
and the Fubini proof of `RightParametrix` only needs the column integral bounds of the kernels
and the integrability of `(b / c) u` (`RightParametrixLp`, no density of tests and no Schur
estimate).

Substituting it for the hypothesis `hid` of `SolvabilitySolution` gives the
solutions of local solvability: for `0 < r < r₀` and `g ∈ L^p(U_r)` (`exists_lp_solution`), resp.
`g ∈ C^α(U_r)` (`exists_holder_solution`), the fixed point `f = g + 𝓕_r f` has
`L̃ v = g` on `U_r` in distributions for `v = P_R E_r f`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section Unconditional

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))

variable {K a b}

/-- **The `L^p` extension of the right-parametrix identity, proved.** For the
fixed cutoffs `a, b` with `a b = a` and the H1 fundamental kernel `K` of the lifted drift chart
`C`, `L̃ P_R u = a u - F_R^chart u` holds in the sense of distributions on `V = C.U` for every
`u ∈ L^p(V)` with `1 ≤ p ≤ ∞`:
`∫_V P_R u · L̃ᵀφ = ∫_V (a u - F_R^chart u) φ` for every test `φ` of `V` (the exact statement
`RightLpIdentity K a b p`). -/
theorem rightLpIdentity (hab : ∀ ξ, a ξ * b ξ = a ξ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    RightLpIdentity K a b p := fun _ hu φ =>
  integral_rightParametrix_mul_transpose_chartError_of_locallyIntegrable hq ν₀ K a b φ
    (locallyIntegrableOn_of_memLp C.isOpen_U hp hu) hab

/-- `RightLpIdentity` for all finite exponents `1 ≤ p < ∞` at once
(the form of the hypothesis `hid` of `exists_lp_solution_of_lpIdentity`). -/
theorem rightLpIdentity_forall (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → RightLpIdentity K a b p := fun _ hp _ => rightLpIdentity hab hp

variable (K a b)

/-- **The `L^p` solution of local solvability.** Let `a b = a` and `a = 1` near
`ξ₀ ∈ C.U`. There is `r₀ > 0` (depending on the chart data only) such that for `0 < r < r₀`,
`1 ≤ p < ∞` and every `g ∈ L^p(U_r)`, `U_r = B̃(ξ₀, r)`, there is `f ∈ L^p(U_r)` with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` almost everywhere on `U_r`, `‖f‖_p ≤ 2 ‖g‖_p`
(unique up to null sets), and `v = P_R E_r f` satisfies `L̃ v = g` on `U_r` in distributions:
`∫_V v L̃ᵀφ = ∫_{U_r} g φ` for every test `φ` of `V` with `tsupport φ ⊆ U_r`. This is
`exists_lp_solution_of_lpIdentity` with the hypothesis `hid` discharged by `rightLpIdentity`. -/
theorem exists_lp_solution (hab : ∀ ξ, a ξ * b ξ = a ξ) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (C.driftBall ξ₀ r)) →
        ∃ f : (Fin (n + m) → ℝ) → ℝ, MemLp f p (volume.restrict (C.driftBall ξ₀ r)) ∧
          f =ᵐ[volume.restrict (C.driftBall ξ₀ r)]
            (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ) ∧
          eLpNorm f p (volume.restrict (C.driftBall ξ₀ r)) ≤
            2 * eLpNorm g p (volume.restrict (C.driftBall ξ₀ r)) ∧
          (∀ f' : (Fin (n + m) → ℝ) → ℝ, MemLp f' p (volume.restrict (C.driftBall ξ₀ r)) →
            f' =ᵐ[volume.restrict (C.driftBall ξ₀ r)]
              (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f') ξ) →
            f' =ᵐ[volume.restrict (C.driftBall ξ₀ r)] f) ∧
          ∀ φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞),
            tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.driftBall ξ₀ r →
            ∫ ξ in C.U, C.rightParametrix K a b ((C.driftBall ξ₀ r).indicator f) ξ *
                sumSquaresWithDriftTranspose C.Xl φ ξ =
              ∫ ξ in C.driftBall ξ₀ r, g ξ * φ ξ :=
  exists_lp_solution_of_lpIdentity K a b hξ₀ ha (rightLpIdentity_forall hab)

/-- **The Hölder solution of local solvability.** Let `a b = a`,
`a = 1` near `ξ₀ ∈ C.U` and `0 < α < 1`. There is `r₀ > 0` (depending on the chart data and `α`
only) such that for `0 < r < r₀` and every `g` of finite `C^α(U_r)`-norm there is `f ∈ C^α(U_r)`
with `f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` on `U_r`,
`‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}` (unique on `U_r`), and `v = P_R E_r f` satisfies `L̃ v = g` on
`U_r` in distributions. This is `exists_holder_solution_of_lpIdentity` with the hypothesis `hid`
discharged by `rightLpIdentity`. -/
theorem exists_holder_solution (hab : ∀ ξ, a ξ * b ξ = a ξ) {ξ₀ : Fin (n + m) → ℝ}
    (hξ₀ : ξ₀ ∈ C.U) (ha : ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ g : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (C.driftBall ξ₀ r) g < ⊤ →
        ∃ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.driftBall ξ₀ r) f < ⊤ ∧
          EqOn f (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ)
            (C.driftBall ξ₀ r) ∧
          holderENorm C.dl α (C.driftBall ξ₀ r) f ≤
            2 * holderENorm C.dl α (C.driftBall ξ₀ r) g ∧
          (∀ f' : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.driftBall ξ₀ r) f' < ⊤ →
            EqOn f' (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f') ξ)
              (C.driftBall ξ₀ r) → EqOn f' f (C.driftBall ξ₀ r)) ∧
          ∀ φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞),
            tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.driftBall ξ₀ r →
            ∫ ξ in C.U, C.rightParametrix K a b ((C.driftBall ξ₀ r).indicator f) ξ *
                sumSquaresWithDriftTranspose C.Xl φ ξ =
              ∫ ξ in C.driftBall ξ₀ r, g ξ * φ ξ :=
  exists_holder_solution_of_lpIdentity K a b hξ₀ ha (rightLpIdentity_forall hab) hα0 hα1

end Unconditional

end RothschildStein.P2
