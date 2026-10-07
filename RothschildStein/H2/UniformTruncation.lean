-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TransposeData
public import RothschildStein.H2.UniformVolume

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Every positive truncation has a bounded kernel on U×U.
Compact-centre lower volumes justify Fubini, rather than pointwise slice
integrability alone (BB p. 311). -/
theorem LocalKernelData.exists_truncated_kernel_bound (Q : LocalKernelData D d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ ball Q.z Q.R, ∀ y ∈ ball Q.z Q.R,
      ε < d.d' x y → |Q.cutoffKernel x y| ≤ M := by
  have hθ : 0 < d.θ₂ := d.θ₁_pos.trans_le d.θ₁_le
  let s := min (ε / d.θ₂) D.κ
  have hs : 0 < s := lt_min (div_pos hε hθ) D.κ_pos
  have hsκ : s ≤ 6 * D.κ := (min_le_right _ _).trans (by linarith [D.κ_pos])
  obtain ⟨m, hm, hmb⟩ := D.outerPatch.exists_uniform_lower hs hsκ
  have hz := D.sub₀₁ Q.center
  have hmt : m < ⊤ := (hmb Q.z hz).trans_lt (D.outerPatch.doubling Q.z hz s hs hsκ).2.1
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm.ne' hmt.ne
  refine ⟨Q.singularA / m.toReal, div_nonneg Q.localized_singular.A_nonneg hmr.le, ?_⟩
  intro x hx y hy hxy
  have hx₁ := Q.supported_localized_singular.sub_G hx
  have hy₁ := Q.supported_localized_singular.sub_G hy
  have hd : ε / d.θ₂ < dist x y := by
    apply (div_lt_iff₀ hθ).mpr
    have hc := (d.comp x hx₁ y hy₁).2
    nlinarith
  have hdp : 0 < dist x y := (div_pos hε hθ).trans hd
  have hupper : dist x y < 2 * Q.R := by
    have ht := dist_triangle x Q.z y
    have hxx : dist x Q.z < Q.R := hx
    have hyz : dist y Q.z < Q.R := hy
    have hyy : dist Q.z y < Q.R := by simpa only [dist_comm] using hyz
    linarith
  have hv := D.outerPatch.doubling x hx₁ (dist x y) hdp
    (by change dist x y ≤ 6 * D.κ; linarith [Q.radius_lt])
  change 0 < volumeAt D.μ x y ∧ volumeAt D.μ x y < ⊤ ∧ _ at hv
  have hmv : m ≤ volumeAt D.μ x y := (hmb x hx₁).trans
    (measure_mono (ball_subset_ball ((min_le_left _ _).trans hd.le)))
  have hreal := ENNReal.toReal_mono hv.2.1.ne hmv
  have hsize := Q.localized_singular.size x hx₁ y hy₁ (dist_pos.mp hdp)
  simp only [kernelWeight, Real.rpow_zero, one_div, ← div_eq_mul_inv] at hsize
  exact hsize.trans (div_le_div_of_nonneg_left Q.localized_singular.A_nonneg hmr hreal)

end RothschildStein.H2
