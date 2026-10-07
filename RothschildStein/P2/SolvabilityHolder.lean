-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityHolderFixed
public import RothschildStein.P1.ParametrixKernelBoundsSol
public import RothschildStein.P1.RestrictedErrorMeasurable

/-!
# Local solvability, Hölder contraction: the restricted error of `F_R^chart` is a `C^α(U_r)` contraction

On a lifted drift chart `C` (fixed cutoffs `a, b`, H1 fundamental kernel `K`), the restricted error
`𝓕_r f = (F_R^chart E_r f)|_{U_r}` is a `HolderBoundedOperator` of the Banach space
`C^α(U_r) = BoundedHolder (chartHolderData ...)` with the Hölder norm
`holderENorm C.dl α U_r` of norm at most `C_α r^(1-α)`, `0 < α < 1`
(`exists_rightChartError_holderBoundedOperator`; the restricted-error Hölder bound, by the direct fractional-kernel
estimate near/far splitting of `RestrictedErrorHolder`). For `r < r₀`, `C_α r^(1-α) ≤ 1/2`, and by
`HolderBoundedOperator.exists_function_fixedPoint` every `g ∈ C^α(U_r)` has a unique solution
`f ∈ C^α(U_r)` of `f = g + 𝓕_r f` with `‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}`
(`exists_holder_fixedPoint`; BB pp. 606–607, proof of Prop 11.61(b)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section Generic

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : P1.LiftedChart w s Ω hΩ X x₀ m} {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
  {rstar : ℝ} {kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} {A B : ℝ}

/-- **Hölder data of a chart ball**: the lifted control distance `d̃`,
the exponent `α > 0` and a subset `V` of the chart domain `U` (on which `d̃` separates points,
`dl_eq_zero_iff`). -/
def chartHolderData (C : P1.LiftedChart w s Ω hΩ X x₀ m) {α : ℝ} (hα : 0 < α)
    (V : Set (Fin (n + m) → ℝ)) (hV : V ⊆ C.U) : HolderData (n + m) where
  d := C.dl
  α := α
  V := V
  α_pos := hα
  sep _ hx _ hy hxy := ((C.dl_eq_zero_iff (hV hx) (hV hy)).mp hxy).symm

/-- A function of finite Hölder norm is bounded on `V`. -/
theorem exists_bound_of_holderENorm_lt_top {d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞} {α : ℝ}
    {V : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (hf : holderENorm d α V f < ⊤) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ V, |f y| ≤ M := by
  have hsup : (⨆ x : V, ENNReal.ofReal |f x|) ≠ ⊤ :=
    ne_top_of_le_ne_top hf.ne (le_self_add (b := holderSeminorm d α V f))
  refine ⟨(⨆ x : V, ENNReal.ofReal |f x|).toReal, ENNReal.toReal_nonneg, fun y hy => ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hsup).mp
    (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨y, hy⟩)

/-- **Additivity of the restricted error on `C^α(U_r)`.** For functions
`f, g` of finite Hölder norm on `U_r` (hence bounded and continuous there),
`𝓕_r (f - g) = 𝓕_r f - 𝓕_r g` on `U_r`: the kernel integrals converge absolutely. -/
theorem restrictedError_sub_eqOn (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) {α : ℝ} (hα0 : 0 < α) {r : ℝ} (hr0 : 0 < r)
    (hrr : r < rstar) {f g : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) f < ⊤)
    (hg : holderENorm C.dl α (rsBall C.O w C.Xl ξ₀ r) g < ⊤) :
    EqOn (C.restrictedError ξ₀ r kk (fun x => f x - g x))
      (fun ξ => C.restrictedError ξ₀ r kk f ξ - C.restrictedError ξ₀ r kk g ξ)
      (rsBall C.O w C.Xl ξ₀ r) := by
  obtain ⟨Cv, hCv, hsetup⟩ := hr.exists_setup hk
  obtain ⟨hshell, hsb, hnull⟩ := hsetup r hr0 hrr
  have hSU : rsBall C.O w C.Xl ξ₀ r ⊆ C.U := fun y hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)
  obtain ⟨Mf, hMf0, hMf⟩ := exists_bound_of_holderENorm_lt_top hf
  obtain ⟨Mg, hMg0, hMg⟩ := exists_bound_of_holderENorm_lt_top hg
  have hfm := aestronglyMeasurable_of_holderENorm_lt_top hSU hshell.measurableSet hα0 hf
  have hgm := aestronglyMeasurable_of_holderENorm_lt_top hSU hshell.measurableSet hα0 hg
  intro ξ hξ
  simp only
  rw [restrictedError_eq hshell.measurableSet hξ (hnull ξ hξ),
    restrictedError_eq hshell.measurableSet hξ (hnull ξ hξ),
    restrictedError_eq hshell.measurableSet hξ (hnull ξ hξ)]
  have hi1 := hsb.integrable_row hshell hfm hMf0 hMf hξ
  have hi2 := hsb.integrable_row hshell hgm hMg0 hMg hξ
  simp only [mul_sub]
  exact integral_sub hi1 hi2

/-- **The restricted error is a bounded operator of `C^α(U_r)`.** For an
admissible radius, the lifted kernel bounds and `0 < α < 1` there is `C_α` such that for every
`0 < r < r_*` the restricted error `𝓕_r` is a `HolderBoundedOperator` of the Hölder space of the
chart ball `U_r` (`chartHolderData`) of norm at most `C_α r^(1-α)` (the restricted-error Hölder bound). -/
theorem exists_restrictedError_holderBoundedOperator (hr : C.IsSmallBallRadius K₀ ξ₀ rstar)
    (hk : C.RestrictedKernelBounds K₀ kk A B) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ (r : ℝ) (hr0 : 0 < r) (hrr : r < rstar),
      HolderBoundedOperator (chartHolderData C hα0 (rsBall C.O w C.Xl ξ₀ r)
        (fun _ hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)))
        (C.restrictedError ξ₀ r kk) (CH * r ^ (1 - α)) := by
  obtain ⟨CH, hCH, h⟩ := exists_restrictedError_holder_bound hr hk hα0 hα1
  refine ⟨CH, hCH, fun r hr0 hrr => ⟨fun f => h r hr0 hrr f, fun f g hfg ξ hξ => ?_,
    fun f g hf hg => restrictedError_sub_eqOn hr hk hα0 hr0 hrr hf hg⟩⟩
  unfold restrictedError
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  by_cases hη : η ∈ rsBall C.O w C.Xl ξ₀ r
  · simp [Set.indicator_of_mem hη, hfg hη]
  · simp [Set.indicator_of_notMem hη]

end Generic

section Drift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
  {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}

/-- The chart ball `U_r` lies in the chart domain. -/
theorem driftBall_subset_U (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r)
    (hrr : r < rstar) : C.driftBall ξ₀ r ⊆ C.U :=
  fun _ hy => hr.subset_U (hr.ball_subset r hr0 hrr hy)

/-- **`‖𝓕_r‖_{C^α → C^α} ≤ C_α r^(1-α)`, for
`𝓕_r f = (F_R^chart E_r f)|_{U_r}`.** For an admissible radius `r_*` and `0 < α < 1` there is
`C_α` such that for every `0 < r < r_*` the map `f ↦ F_R^chart (1_{U_r} f)` is a
`HolderBoundedOperator` of the Hölder space `C^α(U_r)` (`holderENorm` with `d̃`) of norm at
most `C_α r^(1-α)`, with `C_α` independent of `r`. -/
theorem exists_rightChartError_holderBoundedOperator (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ (r : ℝ) (hr0 : 0 < r) (hrr : r < rstar),
      HolderBoundedOperator (chartHolderData C hα0 (C.driftBall ξ₀ r)
        (driftBall_subset_U hr hr0 hrr))
        (fun f ξ => C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ)
        (CH * r ^ (1 - α)) := by
  obtain ⟨A, B, hk⟩ := exists_restrictedKernelBounds_rightChartErrorKernel K a b hK₀ hK₀U
  obtain ⟨CH, hCH, h⟩ := exists_restrictedError_holderBoundedOperator hr hk hα0 hα1
  refine ⟨CH, hCH, fun r hr0 hrr => ?_⟩
  have e : (fun f ξ => C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ) =
      C.restrictedError ξ₀ r (C.rightChartErrorKernel K a b) :=
    funext fun f => (restrictedError_rightChartErrorKernel_eq K a b hr hr0 hrr f).symm
  rw [e]
  exact h r hr0 hrr

/-- The radius with `C r^(1-α) ≤ 1/2`: for `0 < C`, `0 < α < 1` and
`0 < r ≤ (1/(2C))^(1/(1-α))`, `C r^(1-α) ≤ 1/2`. -/
theorem mul_rpow_le_half {C α r : ℝ} (hC : 0 < C) (hα1 : α < 1) (hr : 0 < r)
    (hrr : r ≤ (1 / (2 * C)) ^ (1 / (1 - α))) : C * r ^ (1 - α) ≤ 1 / 2 := by
  have hα' : 0 < 1 - α := by linarith
  have h1 : r ^ (1 - α) ≤ ((1 / (2 * C)) ^ (1 / (1 - α))) ^ (1 - α) :=
    Real.rpow_le_rpow hr.le hrr hα'.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα'.ne', Real.rpow_one] at h1
  calc C * r ^ (1 - α) ≤ C * (1 / (2 * C)) := mul_le_mul_of_nonneg_left h1 hC.le
    _ = 1 / 2 := by field_simp

/-- **The Hölder fixed point `f = g + 𝓕_r f`.** For `0 < α < 1` there
are `C_α > 0` and `0 < r₀ ≤ r_*` with `C_α r₀^(1-α) ≤ 1/2` such that for `0 < r < r₀` and every
`g` of finite norm `‖g‖_{C^α(U_r)} = holderENorm C.dl α U_r g` there is `f` of finite norm with
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` on `U_r` and `‖f‖_{C^α(U_r)} ≤ 2 ‖g‖_{C^α(U_r)}`;
any `f'` of finite norm with the same property equals `f` on `U_r` (BB pp. 606–607,
proof of Prop 11.61(b)). -/
theorem exists_holder_fixedPoint (hK₀ : IsCompact K₀) (hK₀U : K₀ ⊆ C.U)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH r₀ : ℝ, 0 < CH ∧ 0 < r₀ ∧ r₀ ≤ rstar ∧ CH * r₀ ^ (1 - α) ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → r < r₀ → ∀ g : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (C.driftBall ξ₀ r) g < ⊤ →
          ∃ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.driftBall ξ₀ r) f < ⊤ ∧
            EqOn f (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f) ξ)
              (C.driftBall ξ₀ r) ∧
            holderENorm C.dl α (C.driftBall ξ₀ r) f ≤
              2 * holderENorm C.dl α (C.driftBall ξ₀ r) g ∧
            ∀ f' : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α (C.driftBall ξ₀ r) f' < ⊤ →
              EqOn f' (fun ξ => g ξ + C.rightChartError K a b ((C.driftBall ξ₀ r).indicator f') ξ)
                (C.driftBall ξ₀ r) → EqOn f' f (C.driftBall ξ₀ r) := by
  obtain ⟨CH, hCH, h⟩ := exists_rightChartError_holderBoundedOperator K a b hK₀ hK₀U hr hα0 hα1
  have hr' : 0 < (1 / (2 * CH)) ^ (1 / (1 - α)) := by
    have : 0 < 1 - α := by linarith
    positivity
  refine ⟨CH, min rstar ((1 / (2 * CH)) ^ (1 / (1 - α))), hCH, lt_min hr.pos hr', min_le_left _ _,
    mul_rpow_le_half hCH hα1 (lt_min hr.pos hr') (min_le_right _ _), fun r hr0 hrr g hg => ?_⟩
  have hrs : r < rstar := hrr.trans_le (min_le_left _ _)
  have hCr := mul_rpow_le_half hCH hα1 hr0 (hrr.le.trans (min_le_right _ _))
  exact (h r hr0 hrs).exists_function_fixedPoint (by positivity) hCr hg

end Drift

end RothschildStein.P2
