-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.ShellDomination
public import RothschildStein.H2.FractionalConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Absolute convergence of every positive truncation, with the
explicit shell bound of BB Theorem 7.12(a), p. 302. -/
theorem SupportedKernel.truncated_absolute {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    (d : TruncDist D) {ε : ℝ} (hε : 0 < ε) {f : X → ℝ}
    (hf : AEStronglyMeasurable f (D.μ.restrict G)) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M) {x : X} (hx : x ∈ E) :
    IntegrableOn (fun y => K x y * f y) (G ∩ {y | ε < d.d' x y}) D.μ ∧
      (∫⁻ y in G ∩ {y | ε < d.d' x y}, ENNReal.ofReal |K x y * f y| ∂D.μ) ≤
        ENNReal.ofReal (A * R ^ ν * M * D.C_D * (d.θ₂ * R / ε) ^ Real.logb 2 D.C_D) := by
  classical
  let T : Set X := {y | ε < d.d' x y}
  let g : X → ℝ := T.indicator (fun y => K x y * f y)
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hT : MeasurableSet T := measurableSet_lt measurable_const hm
  have hxG := hK.sub_EG hx
  have hθ : 0 < d.θ₂ := d.θ₁_pos.trans_le d.θ₁_le
  have ha : 0 < ε / d.θ₂ := div_pos hε hθ
  have hC : 0 ≤ A * R ^ ν * M :=
    mul_nonneg (mul_nonneg hK.kernel.A_nonneg (Real.rpow_nonneg hK.radius_pos.le _)) hM
  have hbound : (∫⁻ y in G, ENNReal.ofReal |g y| ∂D.μ) ≤
      ENNReal.ofReal (A * R ^ ν * M * D.C_D * (d.θ₂ * R / ε) ^ Real.logb 2 D.C_D) := by
    by_cases haR : ε / d.θ₂ ≤ R
    · have hb := D.outerPatch.lintegral_abs_le_shell (hK.sub_G hxG)
        hK.kernel.measurable_E ha haR
        (hK.radius_le.trans (by change 3 * D.κ ≤ 6 * D.κ; linarith [D.κ_pos])) hC
        (g := g) (by
          intro y hy hr
          by_cases hyT : y ∈ T
          · rw [show g y = K x y * f y from indicator_of_mem hyT _]
            rcases hr with hr | hr
            · have hc := (d.comp x (hK.sub_G hxG) y (hK.sub_G hy)).2
              have ht : ε < d.d' x y := hyT
              have hd := (lt_div_iff₀ hθ).mp hr
              nlinarith
            · rw [hK.support x hx y hy hr, zero_mul]
          · exact indicator_of_notMem hyT _) (by
          filter_upwards [ae_restrict_mem hK.kernel.measurable_E, hfb] with y hy hfy
          intro hya
          by_cases hyT : y ∈ T
          swap
          · simp only [g, indicator_of_notMem hyT, abs_zero]
            exact mul_nonneg hC (kernelWeight_nonneg _ _ _ _)
          rw [show g y = K x y * f y from indicator_of_mem hyT _, abs_mul]
          by_cases hyR : R ≤ dist x y
          · rw [hK.support x hx y hy hyR, abs_zero, zero_mul]
            exact mul_nonneg hC (kernelWeight_nonneg _ _ _ _)
          have hd : 0 < dist x y := ha.trans_le hya
          have hk := hK.kernel.size x hxG y hy (dist_pos.mp hd)
          have hp := Real.rpow_le_rpow hd.le (le_of_not_ge hyR) hK.kernel.ν_nonneg
          change |K x y| * |f y| ≤ A * R ^ ν * M * kernelWeight D.μ 0 x y
          unfold kernelWeight at hk ⊢
          simp only [Real.rpow_zero]
          have hvol : 0 ≤ (volumeAt D.μ x y).toReal := ENNReal.toReal_nonneg
          calc
            _ ≤ A * (dist x y ^ ν / (volumeAt D.μ x y).toReal) * M :=
              mul_le_mul hk hfy (abs_nonneg _) (mul_nonneg hK.kernel.A_nonneg (div_nonneg (Real.rpow_nonneg hd.le _) hvol))
            _ ≤ _ := by
              have he := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hvol) hK.kernel.A_nonneg
              have he' := mul_le_mul_of_nonneg_right he hM
              convert he' using 1; ring)
      change (∫⁻ y in G, ENNReal.ofReal |g y| ∂D.μ) ≤
        ENNReal.ofReal (A * R ^ ν * M * D.C_D * (R / (ε / d.θ₂)) ^ Real.logb 2 D.C_D) at hb
      convert hb using 1
      congr 2
      congr 1
      field_simp
    · have hz : ∀ y ∈ G, g y = 0 := by
        intro y hy
        by_cases hyT : y ∈ T
        swap
        · exact indicator_of_notMem hyT _
        rw [show g y = K x y * f y from indicator_of_mem hyT _]
        have ht : ε < d.d' x y := hyT
        have hc := (d.comp x (hK.sub_G hxG) y (hK.sub_G hy)).2
        have hd : ε / d.θ₂ < dist x y := (div_lt_iff₀ hθ).mpr (by simpa only [mul_comm] using ht.trans_le hc)
        rw [hK.support x hx y hy ((le_of_not_ge haR).trans hd.le), zero_mul]
      have he : (∫⁻ y in G, ENNReal.ofReal |g y| ∂D.μ) = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [ae_restrict_mem hK.kernel.measurable_E] with y hy
        simp only [hz y hy, abs_zero, ENNReal.ofReal_zero, Pi.zero_apply]
      rw [he]
      exact bot_le
  have hi : IntegrableOn g G D.μ := integrableOn_of_subtype_lintegral hK.kernel.measurable_E
    (((hK.kernel.measurable_slice hxG).aestronglyMeasurable.mul
      (aestronglyMeasurable_subtype_of_restrict hK.kernel.measurable_E hf)).indicator
        (hT.preimage measurable_subtype_coe)) (hbound.trans_lt ENNReal.ofReal_lt_top)
  have hgi : IntegrableOn (fun y => K x y * f y) (G ∩ T) D.μ := by
    simpa only [g, inter_comm] using (integrableOn_indicator_iff hT).mp hi
  refine ⟨hgi, ?_⟩
  have he : (∫⁻ y in G, ENNReal.ofReal |g y| ∂D.μ) =
      ∫⁻ y in G ∩ T, ENNReal.ofReal |K x y * f y| ∂D.μ := by
    have hp : (fun y => ENNReal.ofReal |g y|) = T.indicator (fun y => ENNReal.ofReal |K x y * f y|) := by
      funext y
      by_cases hy : y ∈ T <;> simp [g, hy]
    rw [hp, lintegral_indicator hT, Measure.restrict_restrict hT, inter_comm]
  rw [← he]
  exact hbound

end RothschildStein.H2
