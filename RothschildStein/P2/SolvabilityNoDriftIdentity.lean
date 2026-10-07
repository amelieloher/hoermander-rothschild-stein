-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityIdentity
public import RothschildStein.P2.SolvabilityNoDriftLp
public import RothschildStein.P2.SolvabilityNoDriftHolder
public import RothschildStein.P1.RightParametrixNoDrift

/-!
# Local solvability without drift: the consequence `L̃ v = g` on `U_r` for `v = P_R E_r f`, `f = g + 𝓕_r f`

The no-drift counterpart of `SolvabilityIdentity`, for a lifted no-drift chart (alphabet `Fin q`,
all weights one, `L̃ = ∑ᵢ X̃ᵢ²`, transpose `sumSquaresTranspose C.Xl`). Let
`U_r = B̃(ξ₀, r) ⋐ {a = 1}` and `E_r f = 1_{U_r} f`. The two contractions of
`SolvabilityNoDriftLp` and `SolvabilityNoDriftHolder` give `f = g + 𝓕_r f`,
`𝓕_r f = (F_R^chart E_r f)|_{U_r}`. This file derives from the right-parametrix identity
`L̃ P_R u = a u - F_R^chart u` (in distributions), applied to `u = E_r f`, that `v = P_R E_r f`
solves `L̃ v = g` on `U_r` in the sense of distributions: `∫_U v L̃ᵀφ = ∫_{U_r} g φ` for every
test `φ` supported in `U_r` (BB p. 605, Prop 11.61).

* `RightLpIdentityNoDrift K a b p` asserts the identity for every `L^p(V)` input (`V = C.U`),
  distributionally against all tests of `V`.
* `integral_rightParametrix_indicator_eq_noDrift` is the pure algebra of the consequence (no `L^p`
  hypothesis: the identity at `E_r f` is an input).
* `rightParametrix_solves_of_lpIdentity_noDrift` (`L^p` data) and
  `rightParametrix_solves_holder_of_lpIdentity_noDrift` (Hölder data) are the `_of_` consequences;
  `rightParametrix_solves_of_test_noDrift` is the version without `RightLpIdentityNoDrift` when `f`
  is itself a test function supported in `U_r`.
* `exists_solving_ball_setup_noDrift`: the setup `U_r ⋐ {a = 1}` from `a = 1` near `ξ₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open RothschildStein.P1 RothschildStein.P1.LiftedChart
namespace RothschildStein.P2

section Identity

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (a b : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))

/-- **The `L^p` extension of the right-parametrix identity**, at the exponent `p`:
for the fixed cutoffs `a, b` and the H1 fundamental kernel `K` of the lifted no-drift chart `C`, the
identity `L̃ P_R u = a u - F_R^chart u` holds in the sense of distributions on the chart domain
`V = C.U` for **every** input `u ∈ L^p(V)`, i.e.
`∫_V P_R u · L̃ᵀφ = ∫_V (a u - F_R^chart u) φ` for every test function `φ` of `V` (the identity holds for every `L^p` input by test approximation and the `L^p → W^{2,p}`
bounds, not merely for inputs in `W_0`: `P_R f_n → P_R f` in
`W^{2,p}` and `F_R^chart f_n → F_R^chart f` in `L^p`, pass the identity distributionally). The identity
on tests `u` is `integral_rightParametrix_mul_transpose_chartError_noDrift`. -/
def RightLpIdentityNoDrift (p : ℝ≥0∞) : Prop :=
  ∀ u : (Fin (n + m) → ℝ) → ℝ, MemLp u p (volume.restrict C.U) →
    ∀ φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞),
      ∫ ξ in C.U, C.rightParametrixNoDrift K a b u ξ * sumSquaresTranspose C.Xl φ ξ =
        ∫ ξ in C.U, (a ξ * u ξ - C.rightChartErrorNoDrift K a b u ξ) * φ ξ

variable {K a b}

/-- **The consequence, algebraically.** Let `U_r ⊆ C.U` be measurable with
`a = 1` on `U_r`, let `f = g + 𝓕_r f` almost everywhere on `U_r`, where
`𝓕_r f = (F_R^chart (1_{U_r} f))|_{U_r}`, and suppose the right-parametrix identity holds for `u = E_r f = 1_{U_r} f`
against the test `φ`. Then `v = P_R E_r f` satisfies `∫_V v L̃ᵀφ = ∫_{U_r} g φ`, for every test
`φ` with `tsupport φ ⊆ U_r`: `L̃ v = g` on `U_r` in distributions. -/
theorem integral_rightParametrix_indicator_eq_noDrift {U : Set (Fin (n + m) → ℝ)}
    (hUm : MeasurableSet U) (hUC : U ⊆ C.U) (ha1 : ∀ ξ ∈ U, a ξ = 1)
    {f g : (Fin (n + m) → ℝ) → ℝ}
    (hfix : ∀ᵐ ξ ∂(volume.restrict U),
      f ξ = g ξ + C.rightChartErrorNoDrift K a b (U.indicator f) ξ)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (hφ : tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ U)
    (hid : ∫ ξ in C.U, C.rightParametrixNoDrift K a b (U.indicator f) ξ *
        sumSquaresTranspose C.Xl φ ξ =
      ∫ ξ in C.U, (a ξ * U.indicator f ξ - C.rightChartErrorNoDrift K a b (U.indicator f) ξ) * φ ξ) :
    ∫ ξ in C.U, C.rightParametrixNoDrift K a b (U.indicator f) ξ *
        sumSquaresTranspose C.Xl φ ξ = ∫ ξ in U, g ξ * φ ξ := by
  rw [hid]
  have hCm : MeasurableSet C.U := C.isOpen_U.measurableSet
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hCm hUC]
  · refine setIntegral_congr_ae hUm ?_
    filter_upwards [(ae_restrict_iff' hUm).mp hfix] with ξ hξ hξU
    have hξ := hξ hξU
    rw [Set.indicator_of_mem hξU, ha1 ξ hξU, one_mul]
    have : f ξ - C.rightChartErrorNoDrift K a b (U.indicator f) ξ = g ξ := by rw [hξ]; ring
    rw [this]
  · intro ξ hξ
    have hξφ : ξ ∉ tsupport (φ : (Fin (n + m) → ℝ) → ℝ) := fun h => hξ.2 (hφ h)
    rw [image_eq_zero_of_notMem_tsupport hξφ, mul_zero]

/-- The chart ball `U_r` is measurable (`0 < r < r_*`). -/
theorem measurableSet_noDriftBall {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ}
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r) (hrr : r < rstar) :
    MeasurableSet (C.noDriftBall ξ₀ r) := by
  obtain ⟨Cv, hCv, hvol⟩ := hr.volume_bound
  exact (hvol ξ₀ hr.mem r hr0 (by linarith [hr.pos])).1

/-- The chart ball `U_r` has finite volume (`0 < r < r_*`). -/
theorem volume_noDriftBall_ne_top {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
    {rstar : ℝ} (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r) (hrr : r < rstar) :
    volume (C.noDriftBall ξ₀ r) ≠ ⊤ := by
  obtain ⟨Cv, hCv, hvol⟩ := hr.volume_bound
  exact (hvol ξ₀ hr.mem r hr0 (by linarith [hr.pos])).2.1

/-- A function of finite `C^α(U_r)`-norm lies in every `L^p(U_r)`, `p ≤ ∞` (it is
bounded and continuous on `U_r`, which has finite measure). -/
theorem memLp_of_holderENorm_lt_top_noDrift {K₀ : Set (Fin (n + m) → ℝ)} {ξ₀ : Fin (n + m) → ℝ}
    {rstar : ℝ} (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) {r : ℝ} (hr0 : 0 < r) (hrr : r < rstar)
    {α : ℝ} (hα0 : 0 < α) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α (C.noDriftBall ξ₀ r) f < ⊤) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (C.noDriftBall ξ₀ r)) := by
  have hSm := measurableSet_noDriftBall hr hr0 hrr
  have hSU := noDriftBall_subset_U hr hr0 hrr
  have : IsFiniteMeasure (volume.restrict (C.noDriftBall ξ₀ r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (volume_noDriftBall_ne_top hr hr0 hrr)⟩
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_holderENorm_lt_top hf
  have hfm := aestronglyMeasurable_of_holderENorm_lt_top hSU hSm hα0 hf
  exact (MemLp.of_bound hfm M (ae_restrict_of_forall_mem hSm fun y hy => by
    simpa [Real.norm_eq_abs] using hM y hy)).mono_exponent le_top

/-- **`L^p` data: `L̃ v = g` on `U_r`, given the `L^p` identity extension.**
Let `U_r = B̃(ξ₀, r) ⋐ {a = 1}` (`K₀ ⊆ {a = 1}`, `0 < r < r_*`), `p ∈ [1, ∞]`, and assume the exact
the hypothesis `RightLpIdentityNoDrift K a b p`. If `f ∈ L^p(U_r)` satisfies
`f = g + 𝓕_r f = g + (F_R^chart E_r f)|_{U_r}` almost everywhere on `U_r` (the fixed point of
`exists_lp_fixedPoint_noDrift`), then `v = P_R E_r f` satisfies `L̃ v = g` on `U_r` in distributions:
`∫_V v L̃ᵀφ = ∫_{U_r} g φ` for every test `φ` of `V` with `tsupport φ ⊆ U_r`. -/
theorem rightParametrix_solves_of_lpIdentity_noDrift {K₀ : Set (Fin (n + m) → ℝ)}
    {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ} {p : ℝ≥0∞} (hid : RightLpIdentityNoDrift K a b p)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) (ha1 : ∀ ξ ∈ K₀, a ξ = 1) {r : ℝ} (hr0 : 0 < r)
    (hrr : r < rstar) {f g : (Fin (n + m) → ℝ) → ℝ}
    (hf : MemLp f p (volume.restrict (C.noDriftBall ξ₀ r)))
    (hfix : f =ᵐ[volume.restrict (C.noDriftBall ξ₀ r)]
      fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (hφ : tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.noDriftBall ξ₀ r) :
    ∫ ξ in C.U, C.rightParametrixNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ *
        sumSquaresTranspose C.Xl φ ξ = ∫ ξ in C.noDriftBall ξ₀ r, g ξ * φ ξ := by
  have hSm := measurableSet_noDriftBall hr hr0 hrr
  have hSU := noDriftBall_subset_U hr hr0 hrr
  have hmem : MemLp ((C.noDriftBall ξ₀ r).indicator f) p (volume.restrict C.U) := by
    rw [memLp_indicator_iff_restrict hSm, Measure.restrict_restrict hSm,
      Set.inter_eq_left.mpr hSU]
    exact hf
  exact integral_rightParametrix_indicator_eq_noDrift hSm hSU
    (fun ξ hξ => ha1 ξ (hr.ball_subset r hr0 hrr hξ)) hfix φ hφ (hid _ hmem φ)

/-- **Hölder data: `L̃ v = g` on `U_r`, given the `L^p` identity
extension.** Same as `rightParametrix_solves_of_lpIdentity_noDrift` for `f` of finite `C^α(U_r)`-norm with
`f = g + 𝓕_r f` on `U_r` (the fixed point of `exists_holder_fixedPoint_noDrift`): `E_r f` lies in every
finite `L^p(V)` (`memLp_of_holderENorm_lt_top_noDrift`: bounded, `U_r` of finite measure), so
`RightLpIdentityNoDrift K a b p` for any one `p` applies (the `L^p` parametrix identity
still applies, because bounded `f` on a bounded ball belongs to every finite `L^p`). -/
theorem rightParametrix_solves_holder_of_lpIdentity_noDrift {K₀ : Set (Fin (n + m) → ℝ)}
    {ξ₀ : Fin (n + m) → ℝ} {rstar : ℝ} {p : ℝ≥0∞} (hid : RightLpIdentityNoDrift K a b p)
    (hr : C.IsSmallBallRadius K₀ ξ₀ rstar) (ha1 : ∀ ξ ∈ K₀, a ξ = 1) {r : ℝ} (hr0 : 0 < r)
    (hrr : r < rstar) {α : ℝ} (hα0 : 0 < α) {f g : (Fin (n + m) → ℝ) → ℝ}
    (hf : holderENorm C.dl α (C.noDriftBall ξ₀ r) f < ⊤)
    (hfix : EqOn f (fun ξ => g ξ + C.rightChartErrorNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ)
      (C.noDriftBall ξ₀ r))
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (hφ : tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.noDriftBall ξ₀ r) :
    ∫ ξ in C.U, C.rightParametrixNoDrift K a b ((C.noDriftBall ξ₀ r).indicator f) ξ *
        sumSquaresTranspose C.Xl φ ξ = ∫ ξ in C.noDriftBall ξ₀ r, g ξ * φ ξ :=
  rightParametrix_solves_of_lpIdentity_noDrift hid hr ha1 hr0 hrr
    (memLp_of_holderENorm_lt_top_noDrift hr hr0 hrr hα0 hf p)
    (ae_restrict_of_forall_mem (measurableSet_noDriftBall hr hr0 hrr) hfix) φ hφ

end Identity

section Setup

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- **The setup `U_r ⋐ {a = 1}`.** If `a = 1` on a neighborhood of `ξ₀ ∈ C.U`, there is a
compact neighborhood `K₀ ⊆ C.U ∩ {a = 1}` of `ξ₀` and an admissible radius `r_*`
(`IsSmallBallRadius K₀ ξ₀ r_*`), so that `U_r = B̃(ξ₀, r) ⊆ K₀ ⊆ {a = 1}` for `0 < r < r_*`. -/
theorem exists_solving_ball_setup_noDrift {a : (Fin (n + m) → ℝ) → ℝ} {ξ₀ : Fin (n + m) → ℝ}
    (hξ₀ : ξ₀ ∈ C.U) (ha : ∀ᶠ ξ in 𝓝 ξ₀, a ξ = 1) :
    ∃ K₀ : Set (Fin (n + m) → ℝ), IsCompact K₀ ∧ K₀ ⊆ C.U ∧ (∀ ξ ∈ K₀, a ξ = 1) ∧
      ∃ rstar : ℝ, C.IsSmallBallRadius K₀ ξ₀ rstar := by
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.mp ha
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp C.isOpen_U ξ₀ hξ₀
  set ε := min ε₁ ε₂ with hε
  have hε0 : 0 < ε := lt_min hε₁ hε₂
  have hK : Metric.closedBall ξ₀ (ε / 2) ⊆ Metric.ball ξ₀ ε := fun y hy => by
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hy
    linarith
  have hKU : Metric.closedBall ξ₀ (ε / 2) ⊆ C.U := fun y hy =>
    h₂ (Metric.ball_subset_ball (min_le_right _ _) (hK hy))
  have hKa : ∀ ξ ∈ Metric.closedBall ξ₀ (ε / 2), a ξ = 1 := fun y hy =>
    h₁ (Metric.ball_subset_ball (min_le_left _ _) (hK hy))
  have hint : ξ₀ ∈ interior (Metric.closedBall ξ₀ (ε / 2)) :=
    interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
  exact ⟨_, isCompact_closedBall _ _, hKU, hKa, C.exists_isSmallBallRadius (isCompact_closedBall _ _) hKU hint⟩

end Setup

end RothschildStein.P2
