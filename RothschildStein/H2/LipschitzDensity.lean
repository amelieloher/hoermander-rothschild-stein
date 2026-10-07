-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.BoundedLipschitz
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter ENNReal
open scoped NNReal Topology ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] in
/-- Bounded pointwise convergence implies Lp convergence for finite p.
The finite-measure dominated-convergence step in BB Remark 7.8, p. 298. -/
theorem tendsto_eLpNorm_of_uniform_bound {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {F : ℕ → X → ℝ} (hm : ∀ n, Measurable (F n)) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ n x, ‖F n x‖ ≤ M) (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
  have hmeas n : Measurable (fun x => ‖F n x‖ₑ ^ p.toReal) :=
    (hm n).enorm.pow_const _
  have hbound n : (fun x => ‖F n x‖ₑ ^ p.toReal) ≤ᵐ[μ]
      (fun _ => ENNReal.ofReal M ^ p.toReal) := by
    apply ae_of_all
    intro x
    apply ENNReal.rpow_le_rpow _ hpr.le
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hb n x)
  have hfin : (∫⁻ _ : X, ENNReal.ofReal M ^ p.toReal ∂μ) ≠ ⊤ := by
    rw [lintegral_const]
    finiteness
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖F n x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    apply ae_of_all
    intro x
    simpa [Function.comp_def, enorm, ENNReal.zero_rpow_of_pos hpr] using (continuous_rpow_const (y := p.toReal)).continuousAt.tendsto.comp
      (tendsto_coe.mpr (ht x).nnnorm)
  have hi := tendsto_lintegral_of_dominated_convergence _ hmeas hbound hfin hlim
  have ho := (continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp hi
  simpa [Function.comp_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp
    ((hm _).aestronglyMeasurable), ENNReal.zero_rpow_of_pos (inv_pos.mpr hpr)] using ho

/-- A closed-set indicator has bounded Lipschitz approximations in every finite Lp.
BB Remark 7.8, p. 298, with distance cutoffs replacing continuous cutoffs. -/
theorem exists_boundedLipschitz_closed_indicator {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {s : Set X} (hs : IsClosed s) (c : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ g : X → ℝ, eLpNorm (g - s.indicator (fun _ => c)) p μ ≤ ε ∧ BoundedLipschitz g := by
  classical
  by_cases hne : s.Nonempty
  · let F : ℕ → X → ℝ := fun n x => c * closedApprox s n x - s.indicator (fun _ => c) x
    have hm : ∀ n, Measurable (F n) := by
      intro n
      obtain ⟨L, M, hl, hb⟩ := (boundedLipschitz_closedApprox s n).const_mul c
      exact hl.continuous.measurable.sub (measurable_const.indicator hs.measurableSet)
    have hb : ∀ n x, ‖F n x‖ ≤ 2 * |c| := by
      intro n x
      have happrox := closedApprox_bounds s n x
      have hi : |s.indicator (fun _ => c) x| ≤ |c| := by
        by_cases hx : x ∈ s <;> simp [hx]
      dsimp [F]
      calc
        _ ≤ |c * closedApprox s n x| + |s.indicator (fun _ => c) x| := abs_sub _ _
        _ ≤ |c| + |c| := add_le_add (by
          rw [abs_mul, abs_of_nonneg happrox.1]
          exact mul_le_of_le_one_right (abs_nonneg c) happrox.2) hi
        _ = _ := by ring
    have ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 0) := by
      intro x
      have h := ((tendsto_const_nhds (x := c)).mul (tendsto_closedApprox hs hne x)).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => s.indicator (fun _ => c) x) atTop _)
      by_cases hx : x ∈ s <;> simpa [F, hx] using h
    have he := tendsto_eLpNorm_of_uniform_bound (μ := μ) hp₀ hp hm (mul_nonneg (by norm_num) (abs_nonneg c)) hb ht
    obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds hε)).exists
    exact ⟨fun x => c * closedApprox s n x, hn.le,
      (boundedLipschitz_closedApprox s n).const_mul c⟩
  · have hs₀ : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact ⟨fun _ => 0, by simp [hs₀], boundedLipschitz_const 0⟩

/-- Bounded Lipschitz functions are dense in Lp for a finite Borel measure.
BB Remark 7.8, p. 298; regularity and simple-function density are supplied by Mathlib. -/
theorem exists_boundedLipschitz_eLpNorm_sub_le {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ⊤)
    {f : X → ℝ} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → ℝ, eLpNorm (f - g) p μ ≤ ε ∧ BoundedLipschitz g := by
  apply hf.induction_dense hp BoundedLipschitz _ _ hε
  · intro c t ht htμ ε hε
    obtain ⟨δ, δpos, hδ⟩ := exists_Lp_half ℝ μ p hε
    obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c δpos.ne'
    obtain ⟨s, st, hs, hμs⟩ := ht.exists_isClosed_sdiff_lt htμ.ne (ENNReal.coe_pos.mpr ηpos).ne'
    have h₁ : eLpNorm (s.indicator (fun _ => c) - t.indicator (fun _ => c)) p μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
      exact hη _ hμs.le (ht.diff hs.measurableSet).nullMeasurableSet
    obtain ⟨g, hg, hgl⟩ := exists_boundedLipschitz_closed_indicator (μ := μ) hp₀ hp hs c δpos
    refine ⟨g, ?_, hgl⟩
    convert (hδ _ _ hg h₁).le using 2
    ext x
    simp
  · intro f g hf hg
    exact hf.add hg

end RothschildStein.H2
