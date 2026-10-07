-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.DifferentiationConsequences
public import RothschildStein.H2.Patches
public import RothschildStein.H2.MaximalAdapters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
/-- The patch maximal superlevel is open in the whole ambient
space, as needed for Whitney covering (BB Lemma 7.34, p. 323). -/
theorem isOpen_patchMaximal_superlevel (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) (t : ℝ≥0∞) : IsOpen {x | t < patchMaximal μ S ρ f x} := by
  exact (lowerSemicontinuous_patchMaximal μ S ρ f).isOpen_preimage t

/-- The good set bound follows from the exact maximal weak
bound and Lebesgue differentiation, without a pointwise premise about f
(BB Lemma 7.34, pp. 323–324). -/
theorem LocDoubling.good_set_bound_of_maximal_weak_type (D : LocDoubling X)
    (hweak : PatchMaximalWeakType D.μ D.Ω₁ D.Ω₂ D.κ D.C_D)
    (f : X → ℝ) (hf : IntegrableOn f D.Ω₂ D.μ) (t : ℝ≥0∞) :
    ∀ᵐ x ∂D.μ, x ∈ D.Ω₁ →
      x ∉ {x | t < patchMaximal D.μ D.Ω₁ D.κ f x} → ‖f x‖ₑ ≤ t := by
  have hdiff := lebesgue_differentiation_of_maximal_weak_type D.μ D.Ω₁ D.Ω₂
    D.κ D.C_D D.κ_pos D.outerPatch.incl
    (fun x hx r hr hrκ =>
      let hb := D.outerPatch.doubling x hx r hr (by change r ≤ 6 * D.κ; linarith [D.κ_pos])
      ⟨hb.1, hb.2.1⟩)
    ⟨D.open₂.measurableSet, D.finΩ₂⟩ hweak f hf
  filter_upwards [hdiff] with x hx hx₁ hxgood
  exact (hx hx₁).2.2.trans (le_of_not_gt hxgood)

omit [BorelSpace X] in
/-- A maximal superlevel point has a witnessing ball with
strictly larger average (BB Lemma 7.34, p. 323). -/
theorem patchMaximal_superlevel_witness (μ : Measure X) (S : Set X) (ρ : ℝ)
    (f : X → ℝ) {x : X} {t : ℝ≥0∞} (hx : t < patchMaximal μ S ρ f x) :
    ∃ z ∈ S, ∃ r ∈ Ioc 0 ρ, dist x z < r ∧
      t < (⨍⁻ y in ball z r, ‖f y‖ₑ ∂μ) := by
  unfold patchMaximal at hx
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hx
  obtain ⟨hzS, hz⟩ := lt_iSup_iff.mp hz
  obtain ⟨r, hz⟩ := lt_iSup_iff.mp hz
  obtain ⟨hr, hz⟩ := lt_iSup_iff.mp hz
  obtain ⟨hxr, hav⟩ := lt_iSup_iff.mp hz
  exact ⟨z, hzS, r, hr, hxr, hav⟩

/-- Localization of the entire ambient maximal superlevel in
B(x̄,3κ), hence in Ω₁. The support hypothesis holds almost everywhere on Ω₂ (BB Lemma 7.34, pp. 322–323). -/
theorem LocDoubling.maximal_superlevel_location (D : LocDoubling X) {xbar : X}
    (_hxbar : xbar ∈ D.Ω₀) (f : X → ℝ)
    (hsupport : ∀ᵐ y ∂D.μ.restrict D.Ω₂, y ∉ ball xbar D.κ → f y = 0)
    {t : ℝ≥0∞} (ht : 0 < t) :
    {x | t < patchMaximal D.μ D.Ω₁ D.κ f x} ⊆ ball xbar (3 * D.κ) := by
  intro x hx
  obtain ⟨z, hz, r, hr, hxr, hav⟩ :=
    patchMaximal_superlevel_witness D.μ D.Ω₁ D.κ f hx
  by_contra hnot
  have hxfar : 3 * D.κ ≤ dist x xbar := by simpa [mem_ball, not_lt] using hnot
  have hball : ball z r ⊆ D.Ω₂ :=
    (ball_subset_ball (by change r ≤ 6 * D.κ; linarith [hr.2, D.κ_pos])).trans
      (D.outerPatch.incl z hz)
  have hdisj : ∀ y ∈ ball z r, y ∉ ball xbar D.κ := by
    intro y hy hys
    have hzy : dist z y < r := by simpa [mem_ball, dist_comm] using hy
    have hybar : dist y xbar < D.κ := mem_ball.mp hys
    have htr : dist x xbar ≤ dist x z + dist z y + dist y xbar :=
      by linarith [dist_triangle x z xbar, dist_triangle z y xbar]
    linarith [hr.2]
  have hzero : (fun y => ‖f y‖ₑ) =ᵐ[D.μ.restrict (ball z r)] 0 := by
    have hs := hsupport.filter_mono (ae_mono (Measure.restrict_mono hball le_rfl))
    filter_upwards [hs, ae_restrict_mem isOpen_ball.measurableSet] with y hy hym
    simp only [hy (hdisj y hym), enorm_zero, Pi.zero_apply]
  have havzero : (⨍⁻ y in ball z r, ‖f y‖ₑ ∂D.μ) = 0 := by
    rw [setLAverage_eq, lintegral_congr_ae hzero]
    simp only [Pi.zero_apply, lintegral_zero, ENNReal.zero_div]
  rw [havzero] at hav
  exact (ht.trans hav).false

/-- The localized superlevel stays inside the inner open set. -/
theorem LocDoubling.maximal_superlevel_subset_inner (D : LocDoubling X) {xbar : X}
    (hxbar : xbar ∈ D.Ω₀) (f : X → ℝ)
    (hsupport : ∀ᵐ y ∂D.μ.restrict D.Ω₂, y ∉ ball xbar D.κ → f y = 0)
    {t : ℝ≥0∞} (ht : 0 < t) :
    {x | t < patchMaximal D.μ D.Ω₁ D.κ f x} ⊆ D.Ω₁ :=
  (D.maximal_superlevel_location hxbar f hsupport ht).trans
    ((ball_subset_ball (by linarith [D.κ_pos])).trans
      (ball_subset_closedBall.trans (D.incl₀ xbar hxbar)))

end RothschildStein.H2
