-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorEndpoints

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Interpolation combines the weak-(1,1) and weak-(2,2) operator bounds without assuming an Lᵖ conclusion (BB p. 326). -/
theorem operator_lp_below_two_of_weak_one_one (μ : Measure X)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT C p : ℝ}
    (hcT : ‖T‖ ≤ cT) (hC : 0 ≤ C)
    (hweak : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (T v) x) t ≤ ENNReal.ofReal (C / t) * eLpNorm v 1 μ)
    (v : Lp ℝ 2 μ) (hp : 1 < p) (hp2 : p < 2)
    (hvp : MemLp v (ENNReal.ofReal p) μ) :
    MemLp (fun x => (T v) x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => (T v) x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (p * (2 * C / (p - 1) + 4 * cT ^ 2 / (2 - p))) ^ (1 / p) *
          eLpNorm v (ENNReal.ofReal p) μ := by
  have hvmeas : Measurable (fun x => v x) := (Lp.stronglyMeasurable v).measurable
  have hTv := (Lp.aestronglyMeasurable (T v)).aemeasurable
  have hfin := (memLp_iff_moment_lt_top μ hvmeas.aemeasurable (by linarith : 0 < p)).mp hvp
  have hdist : ∀ {t : ℝ}, 0 < t → distribution μ (fun x => (T v) x) t ≤
      ENNReal.ofReal (C / (t / 2)) * moment μ 1 (highPart (fun x => v x) t) +
        ENNReal.ofReal (cT ^ 2 / ((t / 2) ^ (2 : ℝ))) * moment μ 2 (lowPart (fun x => v x) t) := by
    intro t ht
    have hh : MemLp (highPart (fun x => v x) t) 2 μ :=
      (Lp.memLp v).indicator (measurableSet_lt measurable_const
        (by simpa only [Real.norm_eq_abs] using hvmeas.norm))
    have hl : MemLp (lowPart (fun x => v x) t) 2 μ :=
      (Lp.memLp v).indicator (measurableSet_le
        (by simpa only [Real.norm_eq_abs] using hvmeas.norm) measurable_const)
    let vh := hh.toLp (highPart (fun x => v x) t)
    let vl := hl.toLp (lowPart (fun x => v x) t)
    have heq : v = vh + vl := by
      apply Lp.ext
      filter_upwards [hh.coeFn_toLp, hl.coeFn_toLp, Lp.coeFn_add vh vl] with x hx hy hz
      rw [hz]
      change v x = vh x + vl x
      rw [hx, hy]
      exact (congrFun (highPart_add_lowPart (fun x => v x) t) x).symm
    have hs : ∀ᵐ x ∂μ, |(T v) x| ≤ |(T vh) x| + |(T vl) x| := by
      rw [heq, T.map_add]
      filter_upwards [Lp.coeFn_add (T vh) (T vl)] with x hx
      rw [hx]
      change |(T vh) x + (T vl) x| ≤ _
      exact abs_add_le _ _
    have hn1 : eLpNorm vh 1 μ = moment μ 1 (highPart (fun x => v x) t) := by
      rw [eLpNorm_congr_ae hh.coeFn_toLp, moment_one_eq_eLpNorm μ hh.aestronglyMeasurable]
    have hn2 : moment μ 2 vl = moment μ 2 (lowPart (fun x => v x) t) :=
      lintegral_congr_ae (hl.coeFn_toLp.fun_comp fun a : ℝ => ENNReal.ofReal (|a| ^ (2 : ℝ)))
    calc
      _ ≤ distribution μ (fun x => (T vh) x) (t / 2) +
          distribution μ (fun x => (T vl) x) (t / 2) := distribution_add_le μ hs t
      _ ≤ _ := by
        have h1 := hweak vh (t / 2) (by positivity)
        have h2 := operator_weak_two_two μ T hcT vl (by positivity : 0 < t / 2)
        rw [hn1] at h1
        rw [hn2] at h2
        exact add_le_add h1 h2
  have hb := moment_bound_of_finite_split μ μ hvmeas hTv hC (sq_nonneg cT) hp hp2 hfin hdist
  have hb' : moment μ p (fun x => (T v) x) ≤
      ENNReal.ofReal (p * (2 * C / (p - 1) + 4 * cT ^ 2 / (2 - p))) * moment μ p v := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using hb
  exact ⟨memLp_of_moment_bound μ μ hTv (by linarith) hfin hb',
    eLpNorm_le_of_moment_le μ μ hvmeas.aemeasurable hTv (by linarith) hb'⟩

end RothschildStein.H2
