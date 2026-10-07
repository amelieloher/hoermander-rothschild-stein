-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityLpFixed
public import RothschildStein.P1.ParametrixKernelBoundsSol

/-!
# Local solvability, `L^p` contraction: the restricted error of `F_R^chart` is an `L^p(U_r)` contraction

On a lifted drift chart `C`, with the fixed cutoffs `a, b` and the H1 fundamental kernel `K`
(`F_R^chart = -E_R`, `LiftedChart.rightChartError`), the restricted error
`𝓕_r f = (F_R^chart E_r f)|_{U_r}`, `U_r = B̃(ξ₀, r) = C.driftBall ξ₀ r`, `E_r f = 1_{U_r} f`,
is an `LpBoundedOperator` on `L^p(U_r)` of norm at most `C_L r` for every `1 ≤ p < ∞`
(`exists_rightChartError_lpBoundedOperator`; Schur's lemma with the row/column bounds of
the restricted-error bounds, the constant is independent of `p` and `r`). For `r < r₀`,
`C_L r ≤ 1/2`, and then, by `LpBoundedOperator.exists_function_fixedPoint`, for every
`g ∈ L^p(U_r)` there is a unique `f ∈ L^p(U_r)` with `f = g + 𝓕_r f` and `‖f‖_p ≤ 2 ‖g‖_p`
(`exists_lp_fixedPoint`; BB p. 605, proof of Prop 11.61(a)).
The same statement in the Banach space `Lp ℝ p (volume.restrict U_r)` is `exists_lp_contraction`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section Schur

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {S : Set E} {dr : E → E → ℝ} {q : ℕ}
  {ρ Cv : ℝ} {K : E → E → ℝ} {A B : ℝ}

/-- **Schur's lemma as a bounded `L^p`-operator.** If a kernel `K` cut to `S`
has row and column integrals over `S` at most `A (Cv 2^(q+1)) (2ρ) ≤ Λ` (`SliceBounds`,
`ShellData`), then `f ↦ ∫ K(·, y) f(y) dy` is an `LpBoundedOperator` on `L^p(S)` of norm at most
`Λ`, for every `1 ≤ p < ∞`. -/
theorem lpBoundedOperator_of_sliceBounds [SFinite μ] (hS : ShellData μ S dr q ρ Cv)
    (hK : SliceBounds S dr q K A B) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛ' : A * (Cv * 2 ^ (q + 1)) * (2 * ρ) ≤ Λ) {p : ℝ} (hp : 1 ≤ p) :
    LpBoundedOperator (μ.restrict S) (ENNReal.ofReal p)
      (fun f x => ∫ y, K x y * f y ∂(μ.restrict S)) Λ := by
  have hrow : ∀ x, ∫⁻ y, ‖K x y‖ₑ ∂(μ.restrict S) ≤ ENNReal.ofReal Λ := by
    intro x
    by_cases hx : x ∈ S
    · exact (hK.lintegral_enorm_row_le hS hx).trans (ENNReal.ofReal_le_ofReal hΛ')
    · simp [hK.zero_left x _ hx]
  have hcol : ∀ y, ∫⁻ x, ‖K x y‖ₑ ∂(μ.restrict S) ≤ ENNReal.ofReal Λ := by
    intro y
    by_cases hy : y ∈ S
    · exact (hK.lintegral_enorm_column_le hS hy).trans (ENNReal.ofReal_le_ofReal hΛ')
    · simp [hK.zero_right _ y hy]
  have key : ∀ f, MemLp f (ENNReal.ofReal p) (μ.restrict S) →
      MemLp (fun x => ∫ y, K x y * f y ∂(μ.restrict S)) (ENNReal.ofReal p) (μ.restrict S) ∧
        ∀ᵐ x ∂(μ.restrict S), Integrable (fun y => K x y * f y) (μ.restrict S) := fun f hf =>
    integralOperator_memLp_and_integrable_ae (μ.restrict S) (μ.restrict S) K hK.measurable
      (ENNReal.ofReal Λ) (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hrow hcol f
      hp hf
  refine ⟨fun f hf => (key f hf).1, fun f hf => ?_, fun f g hfg => ?_, fun f g hf hg => ?_,
    fun c f hf => ?_⟩
  · have hb := integralOperator_schur_eLpNorm_bound (μ.restrict S) (μ.restrict S) K hK.measurable
      (ENNReal.ofReal Λ) (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hrow hcol
      f hp hf
    have hpos : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ).ne'
    rwa [← ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top, sub_add_cancel,
      ENNReal.rpow_one] at hb
  · rw [integralOperator_eq_of_ae_eq (μ.restrict S) K hfg]
  · filter_upwards [(key f hf).2, (key g hg).2] with x hx hx'
    show ∫ y, K x y * (f - g) y ∂(μ.restrict S) =
      ∫ y, K x y * f y ∂(μ.restrict S) - ∫ y, K x y * g y ∂(μ.restrict S)
    simp only [Pi.sub_apply, mul_sub]
    exact integral_sub hx hx'
  · refine Filter.Eventually.of_forall fun x => ?_
    show ∫ y, K x y * (c • f) y ∂(μ.restrict S) = c * ∫ y, K x y * f y ∂(μ.restrict S)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

end Schur

section Restricted

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : P1.LiftedChart w s Ω hΩ X x₀ m} {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
  {rstar : ℝ} {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}

/-- `1 ≤ p < ∞` as a real exponent. -/
theorem one_le_toReal_of_ne_top {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) : 1 ≤ p.toReal := by
  simpa using ENNReal.toReal_mono hpt hp

/-- **The restricted error is a bounded `L^p(U_r)`-operator.** For an
admissible radius and the lifted kernel bounds, there is `C_L` such that for every `0 < r < r_*`
and every `1 ≤ p < ∞`, `𝓕_r f = (∫ kk(·, η) E_r f(η) dη)|_{U_r}` is an `LpBoundedOperator` on
`L^p(U_r)` of norm at most `C_L r` (independent of `p`; the restricted-error `L^p` bound). -/
theorem exists_restrictedError_lpBoundedOperator (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ r : ℝ, 0 < r → r < rstar → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      LpBoundedOperator (volume.restrict (rsBall C.O w C.Xl ξ₀ r)) p
        (C.restrictedError ξ₀ r kk) (CL * r) := by
  obtain ⟨Cv, hCv, hsetup⟩ := hr.exists_setup hk
  have hA := hk.A_nonneg
  have hC₁ : 0 ≤ Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1) := by positivity
  refine ⟨2 * A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) + 1, by positivity,
    fun r hr0 hrr p hp hpt => ?_⟩
  obtain ⟨hshell, hsb, hnull⟩ := hsetup r hr0 hrr
  have hΛ : 0 < (2 * A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) + 1) * r := by positivity
  have hΛ' : A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * r) ≤
      (2 * A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) + 1) * r := by nlinarith
  have h1 := lpBoundedOperator_of_sliceBounds hshell hsb hΛ hΛ' (p := p.toReal)
    (one_le_toReal_of_ne_top hp hpt)
  rw [ENNReal.ofReal_toReal hpt] at h1
  refine h1.congr_ae fun f => ?_
  refine (ae_restrict_iff' hshell.measurableSet).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  exact restrictedError_eq hshell.measurableSet hx (hnull x hx)

end Restricted

section Drift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
  {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}

/-- **`‖𝓕_r‖_{L^p → L^p} ≤ C_L r`, for `𝓕_r f = (F_R^chart E_r f)|_{U_r}`.**
For an admissible radius `r_*` (`IsSmallBallRadius K₀ ξ₀ r_*`, a compact `K₀ ⊆ U`) there is `C_L`
such that for every `0 < r < r_*` and `1 ≤ p < ∞` the map `f ↦ F_R^chart (1_{U_r} f)` is an
`LpBoundedOperator` on `L^p(U_r)` of norm at most `C_L r`, with `C_L` independent of `r` and `p`. -/
theorem exists_rightChartError_lpBoundedOperator (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ r : ℝ, 0 < r → r < rstar → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      LpBoundedOperator (volume.restrict (C.driftBall ξ₀ r)) p
        (fun f ξ => C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ) (CL * r) := by
  obtain ⟨A, B, hk⟩ := exists_restrictedKernelBounds_rightChartErrorKernel K a b hK₀ hK₀U
  obtain ⟨CL, hCL, h⟩ := exists_restrictedError_lpBoundedOperator hr hk
  refine ⟨CL, hCL, fun r hr0 hrr p hp hpt => ?_⟩
  refine (h r hr0 hrr p hp hpt).congr_ae fun f => ?_
  have e := restrictedError_rightChartErrorKernel_eq K a b hr hr0 hrr f
  exact Filter.Eventually.of_forall fun ξ => by rw [e]

/-- **The `L^p` fixed point `f = g + 𝓕_r f`.** There are `C_L > 0` and
`0 < r₀ ≤ r_*` with `C_L r₀ ≤ 1/2` such that for `0 < r < r₀`, every `1 ≤ p < ∞` and every
`g ∈ L^p(U_r)` there is `f ∈ L^p(U_r)` with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` almost everywhere on `U_r` and
`‖f‖_{L^p(U_r)} ≤ 2 ‖g‖_{L^p(U_r)}`; any `f' ∈ L^p(U_r)` with the same property equals `f`
almost everywhere on `U_r` (BB p. 605, Prop 11.61). -/
theorem exists_lp_fixedPoint (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) :
    ∃ CL r₀ : ℝ, 0 < CL ∧ 0 < r₀ ∧ r₀ ≤ rstar ∧ CL * r₀ ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (C.driftBall ξ₀ r)) →
          ∃ f : (Fin (n + m) → ℝ) → ℝ, MemLp f p (volume.restrict (C.driftBall ξ₀ r)) ∧
            f =ᵐ[volume.restrict (C.driftBall ξ₀ r)]
              (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ) ∧
            eLpNorm f p (volume.restrict (C.driftBall ξ₀ r)) ≤
              2 * eLpNorm g p (volume.restrict (C.driftBall ξ₀ r)) ∧
            ∀ f' : (Fin (n + m) → ℝ) → ℝ, MemLp f' p (volume.restrict (C.driftBall ξ₀ r)) →
              f' =ᵐ[volume.restrict (C.driftBall ξ₀ r)]
                (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f') ξ) →
              f' =ᵐ[volume.restrict (C.driftBall ξ₀ r)] f := by
  obtain ⟨CL, hCL, h⟩ := exists_rightChartError_lpBoundedOperator K a b hK₀ hK₀U hr
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

end Drift

end RothschildStein.P2
