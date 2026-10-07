-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityHolder
public import RothschildStein.P1.ParametrixKernelBoundsNoDriftSol

/-!
# Local solvability without drift, Hölder contraction: the restricted error of `F_R^chart` is a `C^α(U_r)`
contraction

The no-drift counterpart of the chart part of `SolvabilityHolder` (the Hölder data of a chart ball
`chartHolderData`, additivity `restrictedError_sub_eqOn`, the bounded operator
`exists_restrictedError_holderBoundedOperator` and the radius `mul_rpow_le_half` are alphabet
independent and used from there). On a lifted no-drift chart `C` (fixed cutoffs `a, b`, H1
fundamental kernel `K` of the no-drift model), the restricted error
`𝓕_r f = (F_R^chart E_r f)|_{U_r}` is a `HolderBoundedOperator` of the Banach space
`C^α(U_r) = BoundedHolder (chartHolderData ...)` with the Hölder norm
`holderENorm C.dl α U_r` of norm at most `C_α r^(1-α)`, `0 < α < 1`
(`exists_rightChartError_holderBoundedOperator_noDrift`). For `r < r₀`, `C_α r^(1-α) ≤ 1/2`, and by
`HolderBoundedOperator.exists_function_fixedPoint` every `g ∈ C^α(U_r)` has a unique solution
`f ∈ C^α(U_r)` of `f = g + 𝓕_r f` with `‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}`
(`exists_holder_fixedPoint_noDrift`; BB pp. 606–607, proof of Prop 11.61(b)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section NoDrift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
  {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}

/-- The chart ball `U_r` lies in the chart domain. -/
theorem noDriftBall_subset_U (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r)
    (hrr : r < rstar) : C.noDriftBall ξ₀ r ⊆ C.U :=
  fun _ hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)

/-- **`‖𝓕_r‖_{C^α → C^α} ≤ C_α r^(1-α)`, for
`𝓕_r f = (F_R^chart E_r f)|_{U_r}`.** For an admissible radius `r_*` and `0 < α < 1` there is
`C_α` such that for every `0 < r < r_*` the map `f ↦ F_R^chart (1_{U_r} f)` is a
`HolderBoundedOperator` of the Hölder space `C^α(U_r)` (`holderENorm` with `d̃`) of norm at
most `C_α r^(1-α)`, with `C_α` independent of `r`. -/
theorem exists_rightChartError_holderBoundedOperator_noDrift (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ (r : ℝ) (hr0 : 0 < r) (hrr : r < rstar),
      HolderBoundedOperator (chartHolderData C hα0 (C.noDriftBall ξ₀ r)
        (noDriftBall_subset_U hr hr0 hrr))
        (fun f ξ => C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ)
        (CH * r ^ (1 - α)) := by
  obtain ⟨A, B, hk⟩ := exists_restrictedKernelBounds_rightChartErrorKernel_noDrift K a b hK₀ hK₀U
  obtain ⟨CH, hCH, h⟩ := exists_restrictedError_holderBoundedOperator hr hk hα0 hα1
  refine ⟨CH, hCH, fun r hr0 hrr => ?_⟩
  have e : (fun f ξ => C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ) =
      C.restrictedError ξ₀ r (C.rightChartErrorKernelNoDrift K a b) :=
    funext fun f => (restrictedError_rightChartErrorKernel_eq_noDrift K a b hr hr0 hrr f).symm
  rw [e]
  exact h r hr0 hrr

/-- **The Hölder fixed point `f = g + 𝓕_r f`.** For `0 < α < 1` there
are `C_α > 0` and `0 < r₀ ≤ r_*` with `C_α r₀^(1-α) ≤ 1/2` such that for `0 < r < r₀` and every
`g` of finite norm `‖g‖_{C^α(U_r)} = holderENorm C.dl α U_r g` there is `f` of finite norm with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` on `U_r` and `‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}`;
any `f'` of finite norm with the same property equals `f` on `U_r` (BB pp. 606–607,
proof of Prop 11.61(b)). -/
theorem exists_holder_fixedPoint_noDrift (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH r₀ : ℝ, 0 < CH ∧ 0 < r₀ ∧ r₀ ≤ rstar ∧ CH * r₀ ^ (1 - α) ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ g : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (C.noDriftBall ξ₀ r) g < ⊤ →
          ∃ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.noDriftBall ξ₀ r) f < ⊤ ∧
            EqOn f (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ)
              (C.noDriftBall ξ₀ r) ∧
            holderENorm C.dl α (C.noDriftBall ξ₀ r) f ≤
              2 * holderENorm C.dl α (C.noDriftBall ξ₀ r) g ∧
            ∀ f' : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.noDriftBall ξ₀ r) f' < ⊤ →
              EqOn f' (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f') ξ)
                (C.noDriftBall ξ₀ r) → EqOn f' f (C.noDriftBall ξ₀ r) := by
  obtain ⟨CH, hCH, h⟩ := exists_rightChartError_holderBoundedOperator_noDrift K a b hK₀ hK₀U hr hα0 hα1
  have hr' : 0 < (1 / (2 * CH)) ^ (1 / (1 - α)) := by
    have : 0 < 1 - α := by linarith
    positivity
  refine ⟨CH, min rstar ((1 / (2 * CH)) ^ (1 / (1 - α))), hCH, lt_min hr.pos hr', min_le_left _ _,
    mul_rpow_le_half hCH hα1 (lt_min hr.pos hr') (min_le_right _ _), fun r hr0 hrr g hg => ?_⟩
  have hrs : r < rstar := hrr.trans_le (min_le_left _ _)
  have hCr := mul_rpow_le_half hCH hα1 hr0 (hrr.le.trans (min_le_right _ _))
  exact (h r hr0 hrs).exists_function_fixedPoint (by positivity) hCr hg

end NoDrift

end RothschildStein.P2
