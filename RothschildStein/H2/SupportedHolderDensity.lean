-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularL2Extension
public import RothschildStein.H2.Cutoffs
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Bounded Hölder approximations retain a buffered support ball.
The cutoff is one on the original closed ball and zero outside B(z,2r). -/
theorem LocalKernelData.exists_supported_holder_approx (Q : LocalKernelData D d)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (z : X) {r : ℝ} (hr : 0 < r)
    (v : Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)))
    (hv : ∀ᵐ x ∂D.μ.restrict (ball Q.z Q.R), x ∉ ball z r → v x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : holderFunctions δ (ball Q.z Q.R),
      (∀ x, x ∉ ball z (2 * r) → (f : X → ℝ) x = 0) ∧
      ‖holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f - v‖ < ε := by
  obtain ⟨g, hgerr, hg⟩ := exists_boundedHolder_on_open isOpen_ball isBounded_ball
    Q.measure_ball_lt_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hδ₁ (Lp.memLp v) hε
  let χ := ballCutoff z r (2 * r)
  have hr₂ : r < 2 * r := by linarith
  have hχ : BoundedLipschitz χ := ⟨_, 1, ballCutoff_lipschitz hr₂,
    fun x => by
      change |ballCutoff z r (2 * r) x| ≤ (1 : ℝ)
      rw [abs_of_nonneg (ballCutoff_bounds z r (2 * r) x).1]
      exact (ballCutoff_bounds z r (2 * r) x).2⟩
  have hh : BoundedHolder δ (ball Q.z Q.R) (fun x => χ x * g x) :=
    (hχ.boundedHolder hδ₁ isBounded_ball).mul hg
  let f := holderNormalize hh
  let e := holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  have hf : (e f : X → ℝ) =ᵐ[D.μ.restrict (ball Q.z Q.R)] fun x => χ x * g x := by
    filter_upwards [(f.property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top).coeFn_toLp,
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hxu
    have hhx : (f : X → ℝ) x = χ x * g x := by
      change (ball Q.z Q.R).indicator (fun x => χ x * g x) x = _
      exact indicator_of_mem hxu _
    exact hx.trans hhx
  have hχv : ∀ᵐ x ∂D.μ.restrict (ball Q.z Q.R), χ x * v x = v x := by
    filter_upwards [hv] with x hx
    by_cases hxr : x ∈ ball z r
    · rw [show χ x = 1 from ballCutoff_eq_one hr₂ (le_of_lt hxr), one_mul]
    · rw [hx hxr, mul_zero]
  have hn : eLpNorm (e f - v) 2 (D.μ.restrict (ball Q.z Q.R)) < ENNReal.ofReal ε := by
    refine (eLpNorm_mono_ae (Lp.memLp (e f - v)).aestronglyMeasurable ?_).trans_lt hgerr
    filter_upwards [Lp.coeFn_sub (e f) v, hf, hχv] with x hx hfx hχx
    rw [hx]
    simp only [Pi.sub_apply]
    rw [hfx]
    change |χ x * g x - v x| ≤ |v x - g x|
    have he : χ x * g x - v x = χ x * (g x - v x) := by rw [mul_sub, hχx]
    rw [he, abs_mul, abs_of_nonneg (ballCutoff_bounds z r (2 * r) x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (ballCutoff_bounds z r (2 * r) x).2).trans_eq (abs_sub_comm _ _)
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    change (ball Q.z Q.R).indicator (fun x => χ x * g x) x = 0
    have hχx : χ x = 0 := ballCutoff_eq_zero hr₂ (le_of_not_gt hx)
    by_cases hxu : x ∈ ball Q.z Q.R <;> simp [hxu, hχx]
  · rw [Lp.norm_def]
    exact ((ENNReal.toReal_lt_toReal hn.ne_top ENNReal.ofReal_ne_top).mpr hn).trans_eq
      (ENNReal.toReal_ofReal hε.le)

end RothschildStein.H2
