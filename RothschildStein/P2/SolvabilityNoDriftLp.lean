-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityLp
public import RothschildStein.P1.ParametrixKernelBoundsNoDriftSol

/-!
# Local solvability without drift, `L^p` contraction: the restricted error of `F_R^chart` is an `L^p(U_r)` contraction

The no-drift counterpart of the chart part of `SolvabilityLp` (Schur's lemma
`lpBoundedOperator_of_sliceBounds` and the generic restricted-error operator
`exists_restrictedError_lpBoundedOperator` are alphabet independent and used from there). On a
lifted no-drift chart `C` (alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`), with the fixed cutoffs
`a, b` and the H1 fundamental kernel `K` of the no-drift model (`F_R^chart = -E_R`,
`LiftedChart.rightChartErrorNoDrift`), the restricted error `𝓕_r f = (F_R^chart E_r f)|_{U_r}`,
`U_r = B̃(ξ₀, r) = C.noDriftBall ξ₀ r`, `E_r f = 1_{U_r} f`, is an `LpBoundedOperator` on `L^p(U_r)` of
norm at most `C_L r` for every `1 ≤ p < ∞` (`exists_rightChartError_lpBoundedOperator_noDrift`;
Schur's lemma with the row/column bounds of the restricted-error bounds, the constant is
independent of `p` and `r`). For `r < r₀`, `C_L r ≤ 1/2`, and then, by
`LpBoundedOperator.exists_function_fixedPoint`, for every `g ∈ L^p(U_r)` there is a unique
`f ∈ L^p(U_r)` with `f = g + 𝓕_r f` and `‖f‖_p ≤ 2 ‖g‖_p` (`exists_lp_fixedPoint_noDrift`;
BB p. 605, proof of Prop 11.61(a)). The same statement in the Banach
space `Lp ℝ p (volume.restrict U_r)` is `exists_lp_contraction_noDrift`.
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

/-- **`‖𝓕_r‖_{L^p → L^p} ≤ C_L r`, for `𝓕_r f = (F_R^chart E_r f)|_{U_r}`.**
For an admissible radius `r_*` (`IsSmallBallRadius K₀ ξ₀ r_*`, a compact `K₀ ⊆ U`) there is `C_L`
such that for every `0 < r < r_*` and `1 ≤ p < ∞` the map `f ↦ F_R^chart (1_{U_r} f)` is an
`LpBoundedOperator` on `L^p(U_r)` of norm at most `C_L r`, with `C_L` independent of `r` and `p`. -/
theorem exists_rightChartError_lpBoundedOperator_noDrift (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ r : ℝ, 0 < r → r < rstar → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      LpBoundedOperator (volume.restrict (C.noDriftBall ξ₀ r)) p
        (fun f ξ => C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ) (CL * r) := by
  obtain ⟨A, B, hk⟩ := exists_restrictedKernelBounds_rightChartErrorKernel_noDrift K a b hK₀ hK₀U
  obtain ⟨CL, hCL, h⟩ := exists_restrictedError_lpBoundedOperator hr hk
  refine ⟨CL, hCL, fun r hr0 hrr p hp hpt => ?_⟩
  refine (h r hr0 hrr p hp hpt).congr_ae fun f => ?_
  have e := restrictedError_rightChartErrorKernel_eq_noDrift K a b hr hr0 hrr f
  exact Filter.Eventually.of_forall fun ξ => by rw [e]

/-- **The `L^p` fixed point `f = g + 𝓕_r f`.** There are `C_L > 0` and
`0 < r₀ ≤ r_*` with `C_L r₀ ≤ 1/2` such that for `0 < r < r₀`, every `1 ≤ p < ∞` and every
`g ∈ L^p(U_r)` there is `f ∈ L^p(U_r)` with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` almost everywhere on `U_r` and
`‖f‖_{L^p(U_r)} ≤ 2 ‖g‖_{L^p(U_r)}`; any `f' ∈ L^p(U_r)` with the same property equals `f`
almost everywhere on `U_r` (BB p. 605, Prop 11.61). -/
theorem exists_lp_fixedPoint_noDrift (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) :
    ∃ CL r₀ : ℝ, 0 < CL ∧ 0 < r₀ ∧ r₀ ≤ rstar ∧ CL * r₀ ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (C.noDriftBall ξ₀ r)) →
          ∃ f : (Fin (n + m) → ℝ) → ℝ, MemLp f p (volume.restrict (C.noDriftBall ξ₀ r)) ∧
            f =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)]
              (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ) ∧
            eLpNorm f p (volume.restrict (C.noDriftBall ξ₀ r)) ≤
              2 * eLpNorm g p (volume.restrict (C.noDriftBall ξ₀ r)) ∧
            ∀ f' : (Fin (n + m) → ℝ) → ℝ, MemLp f' p (volume.restrict (C.noDriftBall ξ₀ r)) →
              f' =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)]
                (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f') ξ) →
              f' =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)] f := by
  obtain ⟨CL, hCL, h⟩ := exists_rightChartError_lpBoundedOperator_noDrift K a b hK₀ hK₀U hr
  have hr₀ : 0 < min rstar (1 / (2 * CL)) := lt_min hr.pos (by positivity)
  refine ⟨CL, min rstar (1 / (2 * CL)), hCL, hr₀, min_le_left _ _, ?_,
    fun r hr0 hrr p hp hpt g hg => ?_⟩
  · calc CL * min rstar (1 / (2 * CL)) ≤ CL * (1 / (2 * CL)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hCL.le
      _ = 1 / 2 := by field_simp
  have hrs : r < rstar := hrr.trans_le (min_le_left _ _)
  have hCr : CL * r ≤ 1 / 2 := by
    calc CL * r ≤ CL * (1 / (2 * CL)) :=
          mul_le_mul_of_nonneg_left (hrr.le.trans (min_le_right _ _)) hCL.le
      _ = 1 / 2 := by field_simp
  have : Fact (1 ≤ p) := ⟨hp⟩
  exact (h r hr0 hrs p hp hpt).exists_function_fixedPoint (by positivity) hCr hg

end NoDrift

end RothschildStein.P2
