-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothGaugeCutoff
public import RothschildStein.G2.LocalPower
public import RothschildStein.S.IntegrationByParts
public import RothschildStein.S.Transposes

/-!
# First-order integration by parts against a singular function

The cutoff-shell argument of the left and right pole computations ("cutoff-shell model terms
scale as `ε^{-Q}`; multiplied by the correction and integrated this gives `O(ε)`";
"remainder-field shell terms improve by one weight and tend to zero"). For a smooth gauge `ν`
the cutoffs `θ_ε = 1 - χ((ν u)/ε)` vanish on `{ν ≤ ε}` and equal `1` on `{ν ≥ 2ε}`.

`integral_fieldDerivative_mul_test_of_shell`: if a field `V` is smooth on an open set `W` and a
function `h` is smooth on `W ∖ {0}`, with `(V h) φ` and `h (Vᵀ φ)` integrable for a test `φ`
on `W` and the shell bound `|h| |V ν| ≤ M ν^{2-Q}` near `0` (`Q` the homogeneous dimension), then
`∫_W (V h) φ = ∫_W h (Vᵀ φ)`: the boundary term `∫ h (V θ_ε) φ` is dominated by
`ν^{1-Q} 1_{ν ≤ 2ε}` and tends to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1

section Cutoff

variable {N : ℕ} {G : HomogeneousGroup N}

/-- The shell cutoff `θ_ε(u) = 1 - χ(ν u)` of the model gauge: smooth, equal
to `0` on `{ν ≤ ε}`, equal to `1` on `{ν ≥ 2ε}`, with values in `[0, 1]`
(`H3.quasiballProfile ε (3ε)` is `1` for `ρ ≤ ε` and `0` for `ρ ≥ 2ε`). -/
def shellCutoff (ν : G2.HomogeneousNorm G) (ε : ℝ) (u : Fin N → ℝ) : ℝ :=
  1 - H3.quasiballProfile ε (3 * ε) (ν u)

theorem shellCutoff_contDiff (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (shellCutoff ν ε) :=
  contDiff_const.sub (H3.contDiff_radial_quasiballProfile ν hν hε (by linarith))

theorem shellCutoff_eq_zero (ν : G2.HomogeneousNorm G) {ε : ℝ} (hε : 0 < ε) {u : Fin N → ℝ}
    (hu : ν u ≤ ε) : shellCutoff ν ε u = 0 := by
  rw [shellCutoff, H3.quasiballProfile_one (by linarith) hu, sub_self]

theorem shellCutoff_eq_one (ν : G2.HomogeneousNorm G) {ε : ℝ} (hε : 0 < ε) {u : Fin N → ℝ}
    (hu : 2 * ε ≤ ν u) : shellCutoff ν ε u = 1 := by
  rw [shellCutoff, H3.quasiballProfile_zero (by linarith) (by linarith), sub_zero]

theorem shellCutoff_nonneg (ν : G2.HomogeneousNorm G) (ε : ℝ) (u : Fin N → ℝ) :
    0 ≤ shellCutoff ν ε u := by
  have := (H3.quasiballProfile_range ε (3 * ε) (ν u)).2
  unfold shellCutoff
  linarith

theorem shellCutoff_le_one (ν : G2.HomogeneousNorm G) (ε : ℝ) (u : Fin N → ℝ) :
    shellCutoff ν ε u ≤ 1 := by
  have := (H3.quasiballProfile_range ε (3 * ε) (ν u)).1
  unfold shellCutoff
  linarith

/-- A global bound for the derivative of the smooth transition. -/
theorem exists_abs_deriv_smoothTransition_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |deriv Real.smoothTransition x| ≤ A := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (deriv Real.smoothTransition) := hsm.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) (fun x hx => ?_)
    rcases lt_or_ge x 0 with h | h
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.eventuallyEq_of_mem (Iio_mem_nhds h)
          (fun y hy => Real.smoothTransition.zero_of_nonpos (le_of_lt hy))
      rw [e.deriv_eq]
      simp
    · have h1 : 1 < x := by
        by_contra h'
        exact hx ⟨h, not_lt.mp h'⟩
      have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds h1)
          (fun y hy => Real.smoothTransition.one_of_one_le (le_of_lt hy))
      rw [e.deriv_eq]
      simp
  obtain ⟨A, hA⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max A 0, le_max_right _ _, fun x => (hA x).trans (le_max_left _ _)⟩

theorem hasDerivAt_quasiballProfile {ε : ℝ} (hε : 0 < ε) (ρ : ℝ) :
    HasDerivAt (H3.quasiballProfile ε (3 * ε))
      (deriv Real.smoothTransition ((2 * ε - ρ) / ε) * (-1 / ε)) ρ := by
  have e : H3.quasiballProfile ε (3 * ε) = fun ρ => Real.smoothTransition ((2 * ε - ρ) / ε) := by
    funext ρ
    unfold H3.quasiballProfile
    congr 1
    field_simp
    ring
  rw [e]
  have h1 : HasDerivAt (fun ρ : ℝ => (2 * ε - ρ) / ε) (-1 / ε) ρ := by
    have := ((hasDerivAt_id ρ).const_sub (2 * ε)).div_const ε
    simpa using this
  have hsm : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((2 * ε - ρ) / ε))
      ((2 * ε - ρ) / ε) :=
    ((hsm.differentiable (by simp)) _).hasDerivAt
  exact h2.comp ρ h1

/-- Off the closed shell `{ε ≤ ν ≤ 2ε}` the cutoff is locally constant, so
every field derivative of it vanishes. -/
theorem fieldDerivative_shellCutoff_eq_zero (ν : G2.HomogeneousNorm G) {ε : ℝ} (hε : 0 < ε)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {u : Fin N → ℝ} (hu : ν u < ε ∨ 2 * ε < ν u) :
    fieldDerivative V (shellCutoff ν ε) u = 0 := by
  have hcont : Continuous ν := ν.gauge.1
  unfold fieldDerivative
  rcases hu with h | h
  · have hev : shellCutoff ν ε =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds h] with v hv
      exact shellCutoff_eq_zero ν hε (le_of_lt hv)
    rw [hev.fderiv_eq]
    simp
  · have hev : shellCutoff ν ε =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds h] with v hv
      exact shellCutoff_eq_one ν hε (le_of_lt hv)
    rw [hev.fderiv_eq]
    simp

/-- The field derivative of the cutoff is bounded by `(A / ε) |V ν|` away
from the origin, with `A` independent of `ε`. -/
theorem abs_fieldDerivative_shellCutoff_le (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {A : ℝ} (hA : ∀ x, |deriv Real.smoothTransition x| ≤ A) {ε : ℝ} (hε : 0 < ε)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {u : Fin N → ℝ} (hu : u ≠ 0) :
    |fieldDerivative V (shellCutoff ν ε) u| ≤ A / ε * |fieldDerivative V (ν : (Fin N → ℝ) → ℝ) u| := by
  have hνd : DifferentiableAt ℝ (ν : (Fin N → ℝ) → ℝ) u :=
    (hν.contDiffAt (isOpen_compl_singleton.mem_nhds hu)).differentiableAt (by simp)
  have hcomp := (hasDerivAt_quasiballProfile hε (ν u)).comp_hasFDerivAt u hνd.hasFDerivAt
  have hth : HasFDerivAt (shellCutoff ν ε)
      (-((deriv Real.smoothTransition ((2 * ε - ν u) / ε) * (-1 / ε)) •
        fderiv ℝ (ν : (Fin N → ℝ) → ℝ) u)) u := by
    have := hcomp.const_sub 1
    exact this
  have h1 : |deriv Real.smoothTransition ((2 * ε - ν u) / ε) * (-1 / ε)| ≤ A / ε := by
    rw [abs_mul]
    have e : |(-1 / ε)| = 1 / ε := by rw [abs_div, abs_neg, abs_one, abs_of_pos hε]
    rw [e]
    calc |deriv Real.smoothTransition ((2 * ε - ν u) / ε)| * (1 / ε) ≤ A * (1 / ε) :=
          mul_le_mul_of_nonneg_right (hA _) (by positivity)
      _ = A / ε := by ring
  unfold fieldDerivative
  rw [hth.fderiv]
  simp only [neg_apply, smul_apply, smul_eq_mul, abs_neg]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem tendsto_shellCutoff_one (ν : G2.HomogeneousNorm G) {u : Fin N → ℝ} (hu : u ≠ 0) :
    Tendsto (fun ε => shellCutoff ν ε u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hpos : 0 < ν u := G2.gauge_pos ν.gauge hu
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with ε hε
  exact (shellCutoff_eq_one ν hε.1 (by linarith [hε.2])).symm

theorem eventually_fieldDerivative_shellCutoff_eq_zero (ν : G2.HomogeneousNorm G)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {u : Fin N → ℝ} (hu : u ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), fieldDerivative V (shellCutoff ν ε) u = 0 := by
  have hpos : 0 < ν u := G2.gauge_pos ν.gauge hu
  filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with ε hε
  exact fieldDerivative_shellCutoff_eq_zero ν hε.1 V (Or.inr (by linarith [hε.2]))

end Cutoff

section Singular

variable {N : ℕ} {G : HomogeneousGroup N}

/-- A function continuous off the origin is a.e. strongly measurable on a
measurable set. -/
theorem aestronglyMeasurable_restrict_of_continuousOn_diff_zero [NeZero N] {f : (Fin N → ℝ) → ℝ}
    {W : Set (Fin N → ℝ)} (hW : MeasurableSet W) (hf : ContinuousOn f (W ∩ {0}ᶜ)) :
    AEStronglyMeasurable f (volume.restrict W) := by
  have hae : (W \ {0} : Set (Fin N → ℝ)) =ᵐ[volume] W := sdiff_null_ae_eq_self (by simp)
  have h : volume.restrict W = volume.restrict (W ∩ {0}ᶜ) := by
    rw [← Set.sdiff_eq]
    exact (Measure.restrict_congr_set hae).symm
  rw [h]
  exact hf.aestronglyMeasurable (hW.inter isClosed_singleton.isOpen_compl.measurableSet)

/-- The gauge power `ν^{-β}`, `β < Q`, cut off to a gauge ball, is
integrable by the homogeneous power-integrability criterion. -/
theorem integrable_indicator_gauge_rpow (ν : G2.HomogeneousNorm G) {β : ℝ}
    (hβ : β < G.homogeneousDimension) (ρ : ℝ) :
    Integrable (Set.indicator {u | ν u ≤ ρ} fun u => ν u ^ (-β)) := by
  have hloc := (G2.locallyIntegrable_power_iff ν.gauge β).2 hβ
  exact (integrable_indicator_iff (isClosed_le ν.gauge.1 continuous_const).measurableSet).2
    (hloc.integrableOn_isCompact (G2.isCompact_gauge_le ν.gauge ρ))

/-- Real power form of a gauge zpow: for `0 < t`,
`t^(2 - Q) / t = t^(-(Q - 1))`. -/
theorem zpow_two_sub_div_eq_rpow {t : ℝ} (ht : 0 < t) (Q : ℕ) :
    t ^ (2 - (Q : ℤ)) / t = t ^ (-((Q : ℝ) - 1)) := by
  rw [div_eq_mul_inv, ← zpow_sub_one₀ ht.ne']
  have : (-((Q : ℝ) - 1)) = (((2 - (Q : ℤ) - 1 : ℤ)) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]

/-- Dominated convergence for the cut-off: `∫ θ_ε F → ∫ F` for integrable `F`
(the cutoffs are `[0, 1]`-valued and tend to `1` off the origin). -/
theorem tendsto_integral_shellCutoff_mul (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {μ : Measure (Fin N → ℝ)} (hae : ∀ᵐ u ∂μ, u ≠ 0) {F : (Fin N → ℝ) → ℝ}
    (hF : Integrable F μ) :
    Tendsto (fun ε => ∫ u, shellCutoff ν ε u * F u ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, F u ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖F u‖) ?_ ?_ hF.norm ?_
  · filter_upwards [eventually_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (shellCutoff_contDiff ν hν hε).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun u => ?_))
    rw [norm_mul, Real.norm_of_nonneg (shellCutoff_nonneg ν ε u)]
    nlinarith [shellCutoff_le_one ν ε u, norm_nonneg (F u)]
  · filter_upwards [hae] with u hu
    simpa using (tendsto_shellCutoff_one ν hu).mul_const (F u)

/-- First-order integration by parts against a function with a controlled
singularity at the origin. If `V` is smooth on the open set `W`, `h` is smooth on `W ∖ {0}`, `φ`
is a test function on `W`, `(V h) φ` and `h (Vᵀ φ)` are integrable on `W`, and the shell bound
`|h| |V ν| ≤ M ν^{2-Q}` holds on `{0 < ν < ρ} ∩ W` (`Q` the homogeneous dimension), then
`∫_W (V h) φ = ∫_W h (Vᵀ φ)`: no mass is lost in the cutoff shell `{ε ≤ ν ≤ 2ε}`, where
`|h V θ_ε φ| ≲ ν^{1-Q} 1_{ν ≤ 2ε}` (the left and right pole computations, cutoff-shell terms are `O(ε)`). -/
theorem integral_fieldDerivative_mul_test_of_shell (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (W : Opens (Fin N → ℝ)) {V : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (W : Set (Fin N → ℝ)))
    {h : (Fin N → ℝ) → ℝ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h ((W : Set (Fin N → ℝ)) ∩ {0}ᶜ))
    (φ : TestFunction W ℝ (⊤ : ℕ∞))
    (h₁ : IntegrableOn (fun u => fieldDerivative V h u * φ u) (W : Set (Fin N → ℝ)))
    (h₂ : IntegrableOn (fun u => h u * fieldTranspose V φ u) (W : Set (Fin N → ℝ)))
    {ρ M : ℝ} (hρ : 0 < ρ)
    (hshell : ∀ u ∈ (W : Set (Fin N → ℝ)), 0 < ν u → ν u < ρ →
      |h u| * |fieldDerivative V (ν : (Fin N → ℝ) → ℝ) u| ≤
        M * ν u ^ (2 - (G.homogeneousDimension : ℤ))) :
    (∫ u in (W : Set (Fin N → ℝ)), fieldDerivative V h u * φ u) =
      ∫ u in (W : Set (Fin N → ℝ)), h u * fieldTranspose V φ u := by
  classical
  have : NeZero N := ⟨G.dimension_pos.ne'⟩
  obtain ⟨A, hA0, hA⟩ := exists_abs_deriv_smoothTransition_le
  obtain ⟨B, hB⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hWm : MeasurableSet (W : Set (Fin N → ℝ)) := W.isOpen.measurableSet
  have hOpenWz : IsOpen ((W : Set (Fin N → ℝ)) ∩ {0}ᶜ) := W.isOpen.inter isOpen_compl_singleton
  set μ : Measure (Fin N → ℝ) := volume.restrict (W : Set (Fin N → ℝ)) with hμ
  have hae0 : ∀ᵐ u ∂μ, u ≠ 0 := by
    have : ({0} : Set (Fin N → ℝ))ᶜ ∈ ae μ := by
      rw [compl_mem_ae_iff]
      exact measure_mono_null (fun x hx => hx) (by simp)
    exact this
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ρ / 2 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / 2 by linarith)] with ε hε using hε
  have hhmeas : AEStronglyMeasurable h μ :=
    aestronglyMeasurable_restrict_of_continuousOn_diff_zero hWm hh.continuousOn
  -- smoothness of the cut-off product
  have hg : ∀ ε, 0 < ε → ContDiffOn ℝ (⊤ : ℕ∞) (fun u => shellCutoff ν ε u * h u)
      (W : Set (Fin N → ℝ)) := by
    intro ε hε u hu
    by_cases hu0 : u = 0
    · subst hu0
      have hev : (fun u => shellCutoff ν ε u * h u) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt ν.gauge.1 continuous_const).mem_nhds
          (show ν 0 < ε by rw [(ν.gauge.2.2.1 0).mpr rfl]; exact hε)] with v hv
        rw [shellCutoff_eq_zero ν hε (le_of_lt hv), zero_mul]
      exact (contDiffAt_const.congr_of_eventuallyEq hev).contDiffWithinAt
    · have hmem : u ∈ (W : Set (Fin N → ℝ)) ∩ {0}ᶜ := ⟨hu, hu0⟩
      exact (((shellCutoff_contDiff ν hν hε).contDiffAt.mul
        (hh.contDiffAt (hOpenWz.mem_nhds hmem)))).contDiffWithinAt
  -- the three integrals
  let I₁ : ℝ → ℝ := fun ε => ∫ u, shellCutoff ν ε u * (fieldDerivative V h u * φ u) ∂μ
  let I₂ : ℝ → ℝ := fun ε => ∫ u, shellCutoff ν ε u * (h u * fieldTranspose V φ u) ∂μ
  let I₃ : ℝ → ℝ := fun ε => ∫ u, h u * fieldDerivative V (shellCutoff ν ε) u * φ u ∂μ
  have T1 : Tendsto I₁ (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, fieldDerivative V h u * φ u ∂μ)) :=
    tendsto_integral_shellCutoff_mul ν hν hae0 h₁
  have T2 : Tendsto I₂ (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, h u * fieldTranspose V φ u ∂μ)) :=
    tendsto_integral_shellCutoff_mul ν hν hae0 h₂
  -- the shell term
  set Q : ℕ := G.homogeneousDimension with hQ
  let b : (Fin N → ℝ) → ℝ := fun u => 2 * A * |M| * B *
    Set.indicator {u | ν u ≤ ρ} (fun u => ν u ^ (-((Q : ℝ) - 1))) u
  have hbint : Integrable b μ := by
    have h0 := (integrable_indicator_gauge_rpow ν (β := (Q : ℝ) - 1) (by linarith) ρ).const_mul
      (2 * A * |M| * B)
    exact h0.mono_measure Measure.restrict_le_self
  have hb0 : ∀ u, 0 ≤ b u := by
    intro u
    simp only [b]
    refine mul_nonneg (by positivity) ?_
    by_cases hu : u ∈ {u | ν u ≤ ρ}
    · rw [Set.indicator_of_mem hu]
      exact Real.rpow_nonneg (ν.gauge.2.1 u) _
    · rw [Set.indicator_of_notMem hu]
  have hbound : ∀ ε : ℝ, 0 < ε → ε < ρ / 2 →
      ∀ᵐ u ∂μ, ‖h u * fieldDerivative V (shellCutoff ν ε) u * φ u‖ ≤ b u := by
    intro ε hε0 hε1
    refine (ae_restrict_iff' hWm).2 (Filter.Eventually.of_forall (fun u huW => ?_))
    by_cases hz : fieldDerivative V (shellCutoff ν ε) u = 0
    · rw [hz]
      simpa using hb0 u
    · have hshellu : ε ≤ ν u ∧ ν u ≤ 2 * ε := by
        by_contra hcon
        apply hz
        apply fieldDerivative_shellCutoff_eq_zero ν hε0 V
        by_cases h1 : ε ≤ ν u
        · right
          by_contra hh
          exact hcon ⟨h1, not_lt.mp hh⟩
        · left
          exact not_le.mp h1
      have hνpos : 0 < ν u := lt_of_lt_of_le hε0 hshellu.1
      have hu0 : u ≠ 0 := by
        intro h0
        rw [h0, (ν.gauge.2.2.1 0).mpr rfl] at hνpos
        exact lt_irrefl _ hνpos
      have hνρ : ν u < ρ := by linarith [hshellu.2]
      have hsh := hshell u huW hνpos hνρ
      have hcut := abs_fieldDerivative_shellCutoff_le ν hν hA hε0 V hu0
      have hφu : |φ u| ≤ B := by simpa using hB u
      have hindic : Set.indicator {u | ν u ≤ ρ} (fun u => ν u ^ (-((Q : ℝ) - 1))) u =
          ν u ^ (-((Q : ℝ) - 1)) :=
        Set.indicator_of_mem (show u ∈ {u | ν u ≤ ρ} from le_of_lt hνρ) _
      have hε' : A / ε ≤ 2 * A / ν u := by
        rw [div_le_div_iff₀ hε0 hνpos]
        nlinarith [hshellu.2]
      have hpow : ν u ^ (2 - (Q : ℤ)) * (2 * A / ν u) = 2 * A * ν u ^ (-((Q : ℝ) - 1)) := by
        rw [← zpow_two_sub_div_eq_rpow hνpos Q]
        ring
      have hpowpos : 0 < ν u ^ (2 - (Q : ℤ)) := zpow_pos hνpos _
      have hX : |h u| * |fieldDerivative V (ν : (Fin N → ℝ) → ℝ) u| ≤ |M| * ν u ^ (2 - (Q : ℤ)) :=
        hsh.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hpowpos.le)
      simp only [b, hindic]
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |h u| * |fieldDerivative V (shellCutoff ν ε) u| * |φ u|
          ≤ |h u| * (A / ε * |fieldDerivative V (ν : (Fin N → ℝ) → ℝ) u|) * B := by
            gcongr
        _ = A / ε * (|h u| * |fieldDerivative V (ν : (Fin N → ℝ) → ℝ) u|) * B := by ring
        _ ≤ A / ε * (|M| * ν u ^ (2 - (Q : ℤ))) * B :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (div_nonneg hA0 hε0.le)) hB0
        _ ≤ 2 * A / ν u * (|M| * ν u ^ (2 - (Q : ℤ))) * B := by
            have hnn : 0 ≤ |M| * ν u ^ (2 - (Q : ℤ)) := mul_nonneg (abs_nonneg M) hpowpos.le
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε' hnn) hB0
        _ = |M| * B * (ν u ^ (2 - (Q : ℤ)) * (2 * A / ν u)) := by ring
        _ = |M| * B * (2 * A * ν u ^ (-((Q : ℝ) - 1))) := by rw [hpow]
        _ = 2 * A * |M| * B * ν u ^ (-((Q : ℝ) - 1)) := by ring
  have hmeasI3 : ∀ ε : ℝ, 0 < ε →
      AEStronglyMeasurable (fun u => h u * fieldDerivative V (shellCutoff ν ε) u * φ u) μ := by
    intro ε hε
    have hc : ContinuousOn (fieldDerivative V (shellCutoff ν ε)) (W : Set (Fin N → ℝ)) :=
      ((shellCutoff_contDiff ν hν hε).continuous_fderiv (by simp)).continuousOn.clm_apply
        hV.continuousOn
    exact (hhmeas.mul (hc.aestronglyMeasurable hWm)).mul φ.continuous.aestronglyMeasurable
  have T3 : Tendsto I₃ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
      (F := fun ε u => h u * fieldDerivative V (shellCutoff ν ε) u * φ u) (f := fun _ => (0 : ℝ))
      b ?_ ?_ hbint ?_
    · simpa using this
    · filter_upwards [hsmall] with ε hε using hmeasI3 ε hε.1
    · filter_upwards [hsmall] with ε hε using hbound ε hε.1 hε.2
    · filter_upwards [hae0] with u hu
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_fieldDerivative_shellCutoff_eq_zero ν V hu] with ε hε
      rw [hε]
      simp
  -- the identity for small `ε`
  have E : ∀ᶠ ε in 𝓝[>] (0 : ℝ), I₁ ε + I₃ ε = I₂ ε := by
    filter_upwards [hsmall] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    have key := S.integral_fieldDerivative_mul_test W V hV (fun u => shellCutoff ν ε u * h u)
      ((hg ε hε0).of_le (by simp)) φ
    have hint1 : Integrable (fun u => shellCutoff ν ε u * (fieldDerivative V h u * φ u)) μ := by
      refine h₁.bdd_mul (c := 1) ((shellCutoff_contDiff ν hν hε0).continuous.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun u => ?_))
      rw [Real.norm_of_nonneg (shellCutoff_nonneg ν ε u)]
      exact shellCutoff_le_one ν ε u
    have hint3 : Integrable (fun u => h u * fieldDerivative V (shellCutoff ν ε) u * φ u) μ :=
      hbint.mono' (hmeasI3 ε hε0) (hbound ε hε0 hε1)
    have lhs : (∫ u in (W : Set (Fin N → ℝ)),
        fieldDerivative V (fun u => shellCutoff ν ε u * h u) u * φ u) = I₁ ε + I₃ ε := by
      rw [← integral_add hint1 hint3]
      refine integral_congr_ae ?_
      filter_upwards [hae0, (ae_restrict_iff' hWm).2 (Filter.Eventually.of_forall (fun u hu => hu))]
        with u hu0 huW
      have hmem : u ∈ (W : Set (Fin N → ℝ)) ∩ {0}ᶜ := ⟨huW, hu0⟩
      have hdh : DifferentiableAt ℝ h u :=
        (hh.contDiffAt (hOpenWz.mem_nhds hmem)).differentiableAt (by simp)
      have hdθ : DifferentiableAt ℝ (shellCutoff ν ε) u :=
        ((shellCutoff_contDiff ν hν hε0).differentiable (by simp)) u
      rw [S.fieldDerivative_mul V (shellCutoff ν ε) h u hdθ hdh]
      ring
    have rhs : (∫ u in (W : Set (Fin N → ℝ)),
        (shellCutoff ν ε u * h u) * fieldTranspose V φ u) = I₂ ε := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      simp only [mul_assoc]
    rw [← lhs, ← rhs]
    exact key
  have T13 := T1.add T3
  have T2' : Tendsto I₂ (𝓝[>] (0 : ℝ)) (𝓝 (∫ u, fieldDerivative V h u * φ u ∂μ + 0)) :=
    T13.congr' E
  have := tendsto_nhds_unique T2 T2'
  simpa using this.symm


/-- A function that is continuous off the origin on an open set `W`
and bounded by `M ν^d` on `{0 < ν < ρ}` with `-Q < d` is locally integrable on `W` (power
integrals, using the homogeneous power-integrability criterion). -/
theorem locallyIntegrableOn_of_gauge_bound (ν : G2.HomogeneousNorm G) {W : Set (Fin N → ℝ)}
    (hW : IsOpen W) {F : (Fin N → ℝ) → ℝ} (hF : ContinuousOn F (W ∩ {0}ᶜ)) {ρ M : ℝ}
    (hρ : 0 < ρ) {d : ℤ}
    (hd : -(G.homogeneousDimension : ℤ) < d)
    (hb : ∀ u, 0 < ν u → ν u < ρ → |F u| ≤ M * ν u ^ d) :
    LocallyIntegrableOn F W := by
  have : NeZero N := ⟨G.dimension_pos.ne'⟩
  rw [locallyIntegrableOn_iff hW.isLocallyClosed]
  intro K hKW hK
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hnearm : MeasurableSet (K ∩ {u | ν u ≤ ρ / 2}) :=
    hKm.inter (isClosed_le ν.gauge.1 continuous_const).measurableSet
  have hnear : IntegrableOn F (K ∩ {u | ν u ≤ ρ / 2}) := by
    have hβ : -(d : ℝ) < G.homogeneousDimension := by
      have : (-(G.homogeneousDimension : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast hd
      push_cast at this
      linarith
    have hint : Integrable (fun u => |M| * Set.indicator {u | ν u ≤ ρ / 2}
        (fun u => ν u ^ (-(-(d : ℝ)))) u) (volume.restrict (K ∩ {u | ν u ≤ ρ / 2})) :=
      ((integrable_indicator_gauge_rpow ν hβ (ρ / 2)).const_mul |M|).mono_measure
        Measure.restrict_le_self
    have hmeas : AEStronglyMeasurable F (volume.restrict (K ∩ {u | ν u ≤ ρ / 2})) :=
      aestronglyMeasurable_restrict_of_continuousOn_diff_zero hnearm
        (hF.mono (inter_subset_inter_left _ (inter_subset_left.trans hKW)))
    refine hint.mono' hmeas ?_
    refine (ae_restrict_iff' hnearm).2 ?_
    have h0 : ∀ᵐ u ∂(volume : Measure (Fin N → ℝ)), u ≠ 0 := by
      have : ({0} : Set (Fin N → ℝ))ᶜ ∈ ae (volume : Measure (Fin N → ℝ)) := by
        rw [compl_mem_ae_iff]
        simp
      exact this
    filter_upwards [h0] with u hu0 huS
    have hνpos : 0 < ν u := G2.gauge_pos ν.gauge hu0
    have hνρ : ν u < ρ := by linarith [huS.2.out]
    have hbu := hb u hνpos hνρ
    have hindic : Set.indicator {u | ν u ≤ ρ / 2} (fun u => ν u ^ (-(-(d : ℝ)))) u =
        ν u ^ (d : ℝ) := by
      rw [Set.indicator_of_mem (show u ∈ {u | ν u ≤ ρ / 2} from huS.2)]
      simp
    rw [Real.norm_eq_abs]
    simp only [hindic, Real.rpow_intCast]
    exact hbu.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (zpow_pos hνpos d).le)
  have hfarc : IsCompact (K ∩ {u | ρ / 2 ≤ ν u}) :=
    hK.inter_right (isClosed_le continuous_const ν.gauge.1)
  have hfar : IntegrableOn F (K ∩ {u | ρ / 2 ≤ ν u}) := by
    refine ContinuousOn.integrableOn_compact hfarc (hF.mono ?_)
    rintro u ⟨huK, huν⟩
    refine ⟨hKW huK, fun h0 => ?_⟩
    have : ν u = 0 := by rw [show u = 0 from h0]; exact (ν.gauge.2.2.1 0).mpr rfl
    have h2 : ρ / 2 ≤ ν u := huν
    linarith
  have hK' : K = (K ∩ {u | ν u ≤ ρ / 2}) ∪ (K ∩ {u | ρ / 2 ≤ ν u}) := by
    ext u
    constructor
    · intro hu
      rcases le_total (ν u) (ρ / 2) with h | h
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr ⟨hu, h⟩
    · rintro (h | h) <;> exact h.1
  rw [hK']
  exact hnear.union hfar

/-- The integrability hypotheses of
`integral_fieldDerivative_mul_test_of_shell`: such a function times a test function on `W` is
integrable on `W`. -/
theorem integrableOn_mul_test_of_gauge_bound (ν : G2.HomogeneousNorm G) (W : Opens (Fin N → ℝ))
    {F : (Fin N → ℝ) → ℝ} (hF : ContinuousOn F ((W : Set (Fin N → ℝ)) ∩ {0}ᶜ)) {ρ M : ℝ}
    (hρ : 0 < ρ) {d : ℤ}
    (hd : -(G.homogeneousDimension : ℤ) < d)
    (hb : ∀ u, 0 < ν u → ν u < ρ → |F u| ≤ M * ν u ^ d) (φ : TestFunction W ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun u => F u * φ u) (W : Set (Fin N → ℝ)) :=
  (S.integrable_mul_test W (locallyIntegrableOn_of_gauge_bound ν W.isOpen hF hρ hd hb)
    φ).integrableOn

end Singular

end RothschildStein.P1
