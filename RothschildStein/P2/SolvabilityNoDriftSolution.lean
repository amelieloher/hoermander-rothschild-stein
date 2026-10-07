-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityNoDriftIdentity

/-!
# Local solvability without drift: the fixed point `f = g + 𝓕_r f` and the distributional equation
`L̃ P_R E_r f = g` on `U_r`

The no-drift counterpart of `SolvabilitySolution`. The two contractions (`L^p`:
`SolvabilityNoDriftLp`, Hölder: `SolvabilityNoDriftHolder`) combined with the consequence on tests
(`SolvabilityNoDriftIdentity`): on a lifted no-drift chart with fixed cutoffs `a, b` (`a = 1` near
the centre `ξ₀`, `L̃ = ∑ᵢ X̃ᵢ²`), there is `r₀ > 0` such that for `0 < r < r₀` and every datum `g`

* (`exists_lp_solution_of_lpIdentity_noDrift`) `g ∈ L^p(U_r)`, `1 ≤ p < ∞`: the unique
  `f ∈ L^p(U_r)` with `f = g + 𝓕_r f`, `‖f‖_p ≤ 2 ‖g‖_p`, has `v = P_R E_r f` with `L̃ v = g` on
  `U_r` in the sense of distributions;
* (`exists_holder_solution_of_lpIdentity_noDrift`) `g ∈ C^α(U_r)`, `0 < α < 1`: the unique
  `f ∈ C^α(U_r)` with `f = g + 𝓕_r f`, `‖f‖_{C^α} ≤ 2 ‖g‖_{C^α}`, has `L̃ v = g` on `U_r` for
  `v = P_R E_r f`,

Both conclusions use the hypothesis `RightLpIdentityNoDrift K a b p`, the right-parametrix identity
for every `L^p(V)` input. The membership `v ∈ W^{2,p}` (gain theorem) and the interior
regularity `v ∈ C^{2,α}(U_{r/2})` are derived from these fixed points in `SolvabilityFullNoDrift*`; `SolvabilityNoDriftUnconditional` proves the identity
for every admissible `L^p` exponent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section Solution

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))

/-- **The `L^p` solution, assuming the right-parametrix identity.** Let
`a = 1` near `ξ₀ ∈ C.U`. There is `r₀ > 0` (depending on the chart data only) such that for
`0 < r < r₀`, `1 ≤ p < ∞` and every `g ∈ L^p(U_r)`, `U_r = B̃(ξ₀, r)`, there is `f ∈ L^p(U_r)` with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` almost everywhere on `U_r`, `‖f‖_p ≤ 2 ‖g‖_p`
(unique up to null sets), and `v = P_R E_r f` satisfies `L̃ v = g` on `U_r` in distributions:
`∫_V v L̃ᵀφ = ∫_{U_r} g φ` for every test `φ` of `V` with `tsupport φ ⊆ U_r`. The hypothesis `hid` supplies `RightLpIdentityNoDrift K a b p` for every `1 ≤ p < ∞`. -/
theorem exists_lp_solution_of_lpIdentity_noDrift {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1)
    (hid : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → RightLpIdentityNoDrift K a b p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (C.noDriftBall ξ₀ r)) →
        ∃ f : (Fin (n + m) → ℝ) → ℝ, MemLp f p (volume.restrict (C.noDriftBall ξ₀ r)) ∧
          f =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)]
            (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ) ∧
          eLpNorm f p (volume.restrict (C.noDriftBall ξ₀ r)) ≤
            2 * eLpNorm g p (volume.restrict (C.noDriftBall ξ₀ r)) ∧
          (∀ f' : (Fin (n + m) → ℝ) → ℝ, MemLp f' p (volume.restrict (C.noDriftBall ξ₀ r)) →
            f' =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)]
              (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f') ξ) →
            f' =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)] f) ∧
          ∀ φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞),
            tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.noDriftBall ξ₀ r →
            ∫ ξ in C.U, C.rightParametrixNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ *
                sumSquaresTranspose C.Xl φ ξ =
              ∫ ξ in C.noDriftBall ξ₀ r, g ξ * φ ξ := by
  obtain ⟨K₀, hK₀, hK₀U, ha1, rstar, hr⟩ := exists_solving_ball_setup_noDrift hξ₀ ha
  obtain ⟨CL, r₀, hCL, hr₀, hr₀s, -, h⟩ := exists_lp_fixedPoint_noDrift K a b hK₀ hK₀U hr
  refine ⟨r₀, hr₀, fun r hr0 hrr p hp hpt g hg => ?_⟩
  obtain ⟨f, hf, hfix, hnorm, huniq⟩ := h r hr0 hrr p hp hpt g hg
  exact ⟨f, hf, hfix, hnorm, huniq, fun φ hφ =>
    rightParametrix_solves_of_lpIdentity_noDrift (hid p hp hpt) hr ha1 hr0 (hrr.trans_le hr₀s) hf hfix φ
      hφ⟩

/-- **The Hölder solution, assuming the right-parametrix identity.** Let `a = 1` near `ξ₀ ∈ C.U` and `0 < α < 1`. There is `r₀ > 0`
(depending on the chart data and `α` only) such that for `0 < r < r₀` and every `g` of finite
`C^α(U_r)`-norm there is `f ∈ C^α(U_r)` with `f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` on
`U_r`, `‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}` (unique on `U_r`), and `v = P_R E_r f` satisfies
`L̃ v = g` on `U_r` in distributions. (`E_r f` is bounded on the bounded ball `U_r`, so it lies in
every finite `L^p`, and the `L^p` identity extension applies; the interior regularity
`v ∈ C^{2,α}(U_{r/2})` is proved separately, in `SolvabilityFullHolder`.) -/
theorem exists_holder_solution_of_lpIdentity_noDrift {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1)
    (hid : ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → RightLpIdentityNoDrift K a b p) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ g : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (C.noDriftBall ξ₀ r) g < ⊤ →
        ∃ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.noDriftBall ξ₀ r) f < ⊤ ∧
          EqOn f (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ)
            (C.noDriftBall ξ₀ r) ∧
          holderENorm C.dl α (C.noDriftBall ξ₀ r) f ≤
            2 * holderENorm C.dl α (C.noDriftBall ξ₀ r) g ∧
          (∀ f' : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.noDriftBall ξ₀ r) f' < ⊤ →
            EqOn f' (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f') ξ)
              (C.noDriftBall ξ₀ r) → EqOn f' f (C.noDriftBall ξ₀ r)) ∧
          ∀ φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞),
            tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.noDriftBall ξ₀ r →
            ∫ ξ in C.U, C.rightParametrixNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ *
                sumSquaresTranspose C.Xl φ ξ =
              ∫ ξ in C.noDriftBall ξ₀ r, g ξ * φ ξ := by
  obtain ⟨K₀, hK₀, hK₀U, ha1, rstar, hr⟩ := exists_solving_ball_setup_noDrift hξ₀ ha
  obtain ⟨CH, r₀, hCH, hr₀, hr₀s, -, h⟩ := exists_holder_fixedPoint_noDrift K a b hK₀ hK₀U hr hα0 hα1
  refine ⟨r₀, hr₀, fun r hr0 hrr g hg => ?_⟩
  obtain ⟨f, hf, hfix, hnorm, huniq⟩ := h r hr0 hrr g hg
  exact ⟨f, hf, hfix, hnorm, huniq, fun φ hφ =>
    rightParametrix_solves_holder_of_lpIdentity_noDrift (hid 2 (by norm_num) ENNReal.ofNat_ne_top) hr ha1
      hr0 (hrr.trans_le hr₀s) hα0 hf hfix φ hφ⟩

end Solution

end RothschildStein.P2
