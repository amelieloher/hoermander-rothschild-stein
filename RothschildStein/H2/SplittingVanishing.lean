-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Strong vanishing extends to every open shell; support of K₀
itself is essential here (BB Proposition 7.17, p. 307). -/
theorem LocalKernelData.vanishing_all (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    ∫ y in ball Q.z (2 * Q.R) ∩ {y | r₁ < d.d' x y ∧ d.d' x y < r₂}, Q.K₀ x y ∂D.μ = 0 := by
  classical
  by_cases h₂ : r₂ ≤ Q.R'
  · exact Q.vanishing x hx r₁ r₂ h₁ h₁₂ h₂
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hT : MeasurableSet {y | r₁ < d.d' x y} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {y | r₁ < d.d' x y ∧ d.d' x y < r₂} :=
    hT.inter (measurableSet_lt hm measurable_const)
  have hz := Q.truncated_singular_one_eq_zero hx h₁
  unfold truncatedIntegral at hz
  simp only [mul_one] at hz
  rw [← hz, ← setIntegral_indicator hS, ← setIntegral_indicator hT]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro y hy
  by_cases hy₁ : r₁ < d.d' x y
  · by_cases hy₂ : d.d' x y < r₂
    · simp [hy₁, hy₂]
    · have hk := Q.support₀ x hx y hy ((le_of_not_ge h₂).trans (le_of_not_gt hy₂))
      simp [hy₁, hy₂, hk]
  · simp [hy₁]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A bounded Lipschitz cutoff belongs to the exponent-one Hölder space. -/
theorem KernelCutoff.boundedHolder_one {U G : Set X} {L : ℝ≥0} {b : X → ℝ}
    (hb : KernelCutoff U L b) : BoundedHolder 1 G b := by
  have hs := holderSup_le_of_bound (A := G) (fun x _ => by
    rw [abs_of_nonneg (hb.nonneg x)]
    exact hb.le_one x)
  have hh := holderSemi_le_of_bound (δ := 1) (A := G) (H := L) L.coe_nonneg (by
    intro x _ y _
    simpa only [NNReal.coe_one, Real.rpow_one, Real.dist_eq] using hb.lipschitz.dist_le_mul x y)
  exact ENNReal.add_lt_top.mpr ⟨hs.trans_lt ENNReal.ofReal_lt_top, hh.trans_lt ENNReal.ofReal_lt_top⟩

/-- The singular T(1) contribution has the regularized formula.
BB (7.15), p. 307. -/
theorem LocalKernelData.singular_b_limit (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) :
    Filter.Tendsto (fun ε : ℝ => truncatedIntegral D.μ (ball Q.z (2 * Q.R)) d.d' Q.K₀ ε Q.b x)
      (𝓝[>] 0) (𝓝 (regularizedIntegral D.μ (ball Q.z (2 * Q.R)) Q.K₀ Q.b x)) := by
  have ht : Filter.Tendsto
      (fun ε : ℝ => truncatedIntegral D.μ (ball Q.z (2 * Q.R)) d.d' Q.K₀ ε (fun _ => 1) x)
      (𝓝[>] 0) (𝓝 0) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (Q.truncated_singular_one_eq_zero hx hε).symm
  simpa only [zero_mul, add_zero] using Q.supported_singular.principalValue_limit d
    (δ := 1) (by norm_num) Q.cutoff_b.boundedHolder_one hx ht

end RothschildStein.H2
