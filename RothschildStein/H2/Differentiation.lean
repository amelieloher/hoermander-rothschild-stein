-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocalAverage

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace RothschildStein.H2

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The patch maximal function has the weak (1,1) bound of BB Theorem 7.25, p. 314. The norm is taken on W. -/
def PatchMaximalWeakType (μ : Measure X) (S W : Set X) (ρ C : ℝ) : Prop :=
  ∀ f : X → ℝ, IntegrableOn f W μ → ∀ t : ℝ, 0 < t →
    μ {x | ENNReal.ofReal t < patchMaximal μ S ρ f x} ≤
      ((ENNReal.ofReal C) ^ 3 / ENNReal.ofReal t) * eLpNorm f 1 (μ.restrict W)

private theorem measure_bad_oscillation_eq_zero_of_maximal_weak_type
    (μ : Measure X) (S W : Set X) (ρ C : ℝ) (hρ : 0 < ρ)
    (hballs : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ ρ →
      0 < μ (ball x r) ∧ μ (ball x r) < ⊤)
    (hW : μ W < ⊤) (hweak : PatchMaximalWeakType μ S W ρ C)
    (f : X → ℝ) (hf : IntegrableOn f W μ) (ε : ℝ) (hε : 0 < ε) :
    (μ.restrict W) {x | x ∈ S ∧ ¬ ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤ ENNReal.ofReal ε} = 0 := by
  let ν := μ.restrict W
  let B := {x | x ∈ S ∧ ¬ ∀ᶠ r in 𝓝[>] (0 : ℝ),
    (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤ ENNReal.ofReal ε}
  let a := ENNReal.ofReal (ε / 3)
  have ha : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  let K := (ENNReal.ofReal C) ^ 3
  let L := K / a + 1 / a
  have hLt : L ≠ ⊤ := by
    dsimp [L]
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.div_ne_top (by simp [K]) ha
    · exact ENNReal.div_ne_top (by simp) ha
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hW⟩
  have hbound (g : X →ᵇ ℝ) (hg : MemLp (g : X → ℝ) 1 ν) :
      ν B ≤ L * eLpNorm (f - (g : X → ℝ)) 1 ν := by
    have he : Integrable (f - (g : X → ℝ)) ν := hf.sub (memLp_one_iff_integrable.mp hg)
    have hsub : B ⊆ {x | a < patchMaximal μ S ρ (f - (g : X → ℝ)) x} ∪
        {x | a ≤ ‖f x - g x‖ₑ} := by
      intro x hx
      by_contra hn
      have hm : patchMaximal μ S ρ (f - (g : X → ℝ)) x ≤ a :=
        not_lt.mp (not_or.mp hn).1
      have hp : ‖f x - g x‖ₑ ≤ a := by
        exact (not_le.mp (not_or.mp hn).2).le
      apply hx.2
      filter_upwards [continuous_eventually_laverage_sub_le μ g g.continuous.continuousAt
        (show 0 < ε / 3 by positivity), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hρ)] with r hcont hr hrρ
      have hb := hballs x hx.1 r hr hrρ.le
      calc
        (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤
            patchMaximal μ S ρ (f - (g : X → ℝ)) x +
              (⨍⁻ y in ball x r, ‖g y - g x‖ₑ ∂μ) + ‖f x - g x‖ₑ :=
          laverage_sub_le_approximation μ S ρ f g hx.1 hr hrρ.le g.continuous hb.1.ne' hb.2.ne
        _ ≤ a + a + a := by gcongr
        _ = ENNReal.ofReal ε := by
          dsimp [a]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
    calc
      ν B ≤ ν ({x | a < patchMaximal μ S ρ (f - (g : X → ℝ)) x} ∪
          {x | a ≤ ‖f x - g x‖ₑ}) := measure_mono hsub
      _ ≤ ν {x | a < patchMaximal μ S ρ (f - (g : X → ℝ)) x} +
          ν {x | a ≤ ‖f x - g x‖ₑ} := measure_union_le _ _
      _ ≤ (K / a) * eLpNorm (f - (g : X → ℝ)) 1 ν +
          eLpNorm (f - (g : X → ℝ)) 1 ν / a := by
        apply add_le_add
        · exact (Measure.restrict_le_self _).trans (hweak _ he (ε / 3) (by positivity))
        · exact (meas_ge_le_lintegral_div he.aestronglyMeasurable.enorm ha hat).trans
            (by rw [eLpNorm_one_eq_lintegral_enorm he.aestronglyMeasurable])
      _ = L * eLpNorm (f - (g : X → ℝ)) 1 ν := by
        simp only [L, div_eq_mul_inv, one_mul, add_mul, mul_comm a⁻¹]
  have hle (n : ℕ) : ν B ≤ L * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    obtain ⟨g, hgnorm, hg⟩ := (memLp_one_iff_integrable.mpr hf).exists_boundedContinuous_eLpNorm_sub_le
      (by simp) (show ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 by simp)
    exact (hbound g hg).trans (by gcongr)
  have ht : Tendsto (fun n : ℕ => L * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := L)
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (Or.inr hLt)
  exact bot_unique (ge_of_tendsto ht (Eventually.of_forall hle))

/-- Lebesgue differentiation on a patch follows from the weak (1,1) maximal bound (BB Theorem 7.27, pp. 314–316). Bounded continuous approximations handle the boundary issue on p. 315; this argument needs only positive finite small-ball measures. -/
theorem ae_tendsto_laverage_sub_of_maximal_weak_type
    (μ : Measure X) (S W : Set X) (ρ C : ℝ) (hρ : 0 < ρ)
    (hinside : ∀ x ∈ S, ball x (6 * ρ) ⊆ W)
    (hballs : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r ≤ ρ →
      0 < μ (ball x r) ∧ μ (ball x r) < ⊤)
    (hW : MeasurableSet W ∧ μ W < ⊤) (hweak : PatchMaximalWeakType μ S W ρ C)
    (f : X → ℝ) (hf : IntegrableOn f W μ) :
    ∀ᵐ x ∂μ, x ∈ S → Tendsto
      (fun r : ℝ => ⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hn (n : ℕ) : ∀ᵐ x ∂μ.restrict W, x ∈ S →
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    simpa only [ae_iff, not_imp] using
      measure_bad_oscillation_eq_zero_of_maximal_weak_type μ S W ρ C hρ hballs hW.2
        hweak f hf (1 / (n + 1 : ℝ)) (by positivity)
  have hall := ae_all_iff.mpr hn
  have hSW : S ⊆ W := fun x hx => hinside x hx (mem_ball_self (by positivity))
  have hlocal : ∀ᵐ x ∂μ.restrict W, x ∈ S → Tendsto
      (fun r : ℝ => ⨍⁻ y in ball x r, ‖f y - f x‖ₑ ∂μ) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hall] with x hx hxS
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    by_cases ht : ε = ⊤
    · simp [ht]
    have hreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hreal
    filter_upwards [hx n hxS] with r hr
    exact hr.trans (((ENNReal.ofReal_lt_ofReal_iff hreal).mpr hn).le.trans
      (by rw [ENNReal.ofReal_toReal ht]))
  filter_upwards [(ae_restrict_iff' hW.1).mp hlocal] with x hx hxS
  exact hx (hSW hxS) hxS

end RothschildStein.H2
