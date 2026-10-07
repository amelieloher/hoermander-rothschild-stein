-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.PrincipalValueAway
public import RothschildStein.H2.L2KernelPairing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Buffered kernel slice at a far output point. -/
def LocalKernelData.awayKernel (Q : LocalKernelData D d) (z : X) (r : ℝ) (y : X) : X → ℝ :=
  (ball z (2 * r)).indicator (Q.cutoffKernel y)

/-- The buffered kernel slice belongs to L²(U). The proof uses
only separation and positive finite local volumes. -/
theorem LocalKernelData.awayKernel_memLp (Q : LocalKernelData D d)
    (z : X) {r : ℝ} (hr : 0 < r) (hrκ : r ≤ D.κ / 5) {y : X}
    (hy : y ∈ ball Q.z Q.R) (hyfar : y ∉ ball z (4 * r)) :
    MemLp (Q.awayKernel z r y) 2 (D.μ.restrict (ball Q.z Q.R)) := by
  have hy₁ := Q.supported_localized_singular.sub_G hy
  have hv := D.outerPatch.doubling y hy₁ (2 * r) (by linarith)
    (by change 2 * r ≤ 6 * D.κ; linarith [D.κ_pos])
  change 0 < D.μ (ball y (2 * r)) ∧ D.μ (ball y (2 * r)) < ⊤ ∧ _ at hv
  have hvr : 0 < (D.μ (ball y (2 * r))).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  let M := Q.singularA / (D.μ (ball y (2 * r))).toReal
  have hM : 0 ≤ M := div_nonneg Q.localized_singular.A_nonneg hvr.le
  have hm : AEStronglyMeasurable (Q.awayKernel z r y) (D.μ.restrict (ball Q.z Q.R)) := by
    have hslice := Q.supported_localized_singular.kernel.measurable_slice hy
    have hs : Measurable (fun x : ball Q.z Q.R => Q.awayKernel z r y x) :=
      hslice.indicator (isOpen_ball.measurableSet.preimage measurable_subtype_coe)
    have he : AEStronglyMeasurable (Q.awayKernel z r y)
        (Measure.map Subtype.val (D.μ.comap Subtype.val : Measure (ball Q.z Q.R))) :=
      (MeasurableEmbedding.subtype_coe isOpen_ball.measurableSet).aestronglyMeasurable_map_iff.mpr hs.aestronglyMeasurable
    simpa only [map_comap_subtype_coe isOpen_ball.measurableSet] using he
  let : IsFiniteMeasure (D.μ.restrict (ball Q.z Q.R)) := ⟨by simpa using Q.measure_ball_lt_top⟩
  apply MemLp.of_bound hm M
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
  by_cases hxb : x ∈ ball z (2 * r)
  · change |(ball z (2 * r)).indicator (Q.cutoffKernel y) x| ≤ M
    rw [indicator_of_mem hxb]
    have hd := dist_gt_two_radius hxb hyfar
    have hpos : 0 < dist y x := by linarith
    have hsize := Q.supported_localized_singular.kernel.size y hy x hx (dist_pos.mp hpos)
    have hupper : dist y x < 2 * Q.R := by
      have hxx : dist x Q.z < Q.R := hx
      have hyy : dist y Q.z < Q.R := hy
      have ht := dist_triangle y Q.z x
      rw [dist_comm Q.z x] at ht
      linarith
    have hvx := D.outerPatch.doubling y hy₁ (dist y x) hpos
      (by change dist y x ≤ 6 * D.κ; linarith [Q.radius_lt])
    have hvreal : (D.μ (ball y (2 * r))).toReal ≤ (volumeAt D.μ y x).toReal :=
      ENNReal.toReal_mono hvx.2.1.ne (measure_mono (ball_subset_ball hd.le))
    simp only [kernelWeight, Real.rpow_zero, one_div, ← div_eq_mul_inv] at hsize
    exact hsize.trans (div_le_div_of_nonneg_left Q.localized_singular.A_nonneg hvr hvreal)
  · change |(ball z (2 * r)).indicator (Q.cutoffKernel y) x| ≤ M
    simpa only [indicator_of_notMem hxb, abs_zero] using hM

/-- The ordinary far integral is an L² pairing for every supported input. -/
theorem LocalKernelData.away_integral_pairing (Q : LocalKernelData D d)
    (z : X) {r : ℝ} (hr : 0 < r) (hrκ : r ≤ D.κ / 5) {y : X}
    (hy : y ∈ ball Q.z Q.R) (hyfar : y ∉ ball z (4 * r)) {f : X → ℝ}
    (hf : MemLp f 2 (D.μ.restrict (ball Q.z Q.R)))
    (hs : ∀ᵐ x ∂D.μ.restrict (ball Q.z Q.R), x ∉ ball z (2 * r) → f x = 0) :
    IntegrableOn (fun x => Q.cutoffKernel y x * f x) (ball Q.z Q.R) D.μ ∧
      (∫ x in ball Q.z Q.R, Q.cutoffKernel y x * f x ∂D.μ) =
        inner ℝ ((Q.awayKernel_memLp z hr hrκ hy hyfar).toLp (Q.awayKernel z r y)) (hf.toLp f) := by
  have hk := Q.awayKernel_memLp z hr hrκ hy hyfar
  have he : (fun x => Q.awayKernel z r y x * f x) =ᵐ[D.μ.restrict (ball Q.z Q.R)]
      (fun x => Q.cutoffKernel y x * f x) := by
    filter_upwards [hs] with x hx
    by_cases hxb : x ∈ ball z (2 * r)
    · simp only [LocalKernelData.awayKernel, indicator_of_mem hxb]
    · simp only [LocalKernelData.awayKernel, indicator_of_notMem hxb, hx hxb, mul_zero]
  have hi := l2_kernel_pairing hk hf
  exact ⟨hi.1.congr he, (integral_congr_ae he).symm.trans hi.2⟩

end RothschildStein.H2
