-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularL2Extension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

omit [MeasurableSpace X] [BorelSpace X] in
/-- The buffered input ball is metrically separated from a far output point. -/
theorem dist_gt_two_radius {z x y : X} {r : ℝ}
    (hx : x ∈ ball z (2 * r)) (hy : y ∉ ball z (4 * r)) : 2 * r < dist y x := by
  have hxz : dist x z < 2 * r := hx
  have hyz : 4 * r ≤ dist y z := le_of_not_gt hy
  have ht := dist_triangle y x z
  linarith

/-- For a supported Hölder input, the PV is an absolutely
convergent ordinary integral at every far output point. -/
theorem LocalKernelData.principalValue_away (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    (z : X) {r : ℝ} (hr : 0 < r)
    (hs : ∀ x, x ∉ ball z (2 * r) → f x = 0) {y : X}
    (hy : y ∈ ball Q.z Q.R) (hyfar : y ∉ ball z (4 * r)) :
    IntegrableOn (fun x => Q.cutoffKernel y x * f x) (ball Q.z Q.R) D.μ ∧
      Q.principalValue f y = ∫ x in ball Q.z Q.R, Q.cutoffKernel y x * f x ∂D.μ := by
  let ε₀ := d.θ₁ * r
  have hε₀ : 0 < ε₀ := mul_pos d.θ₁_pos hr
  have hcut : ∀ ε : ℝ, ε < ε₀ → ∀ x ∈ ball Q.z Q.R,
      ¬ε < d.d' y x → f x = 0 := by
    intro ε he x hx hn
    apply hs
    intro hxb
    have hd := dist_gt_two_radius hxb hyfar
    have hc := (d.comp y (Q.supported_localized_singular.sub_G hy)
      x (Q.supported_localized_singular.sub_G hx)).1
    have hn' := le_of_not_gt hn
    dsimp [ε₀] at he
    nlinarith [d.θ₁_pos]
  have hm : ∀ ε : ℝ, MeasurableSet {x | ε < d.d' y x} := fun ε =>
    measurableSet_lt measurable_const (d.meas.comp (measurable_const.prodMk measurable_id))
  have hmid : 0 < ε₀ / 2 := by linarith
  have hi := (Q.supported_localized_singular.truncated_absolute d hmid
    (hf.aestronglyMeasurable_restrict hδ isOpen_ball.measurableSet)
    (M := (holderSup (ball Q.z Q.R) f).toReal) ENNReal.toReal_nonneg
    (by filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
        exact abs_le_holderSup hf.parts.1 hx) hy).1
  have hind : IntegrableOn ({x | ε₀ / 2 < d.d' y x}.indicator
      (fun x => Q.cutoffKernel y x * f x)) (ball Q.z Q.R) D.μ := by
    apply (integrableOn_indicator_iff (hm _)).mpr
    simpa only [inter_comm] using hi
  have heq : EqOn ({x | ε₀ / 2 < d.d' y x}.indicator (fun x => Q.cutoffKernel y x * f x))
      (fun x => Q.cutoffKernel y x * f x) (ball Q.z Q.R) := by
    intro x hx
    dsimp only
    by_cases hc : ε₀ / 2 < d.d' y x
    · simp only [Set.indicator, mem_ofPred_eq, hc, ite_true]
    · simp only [Set.indicator, mem_ofPred_eq, hc, ite_false,
        hcut _ (by linarith) x hx hc, mul_zero]
  have hi' : IntegrableOn (fun x => Q.cutoffKernel y x * f x) (ball Q.z Q.R) D.μ :=
    hind.congr (ae_restrict_of_forall_mem isOpen_ball.measurableSet heq)
  refine ⟨hi', ?_⟩
  have ht : Tendsto (fun ε : ℝ => truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f y)
      (𝓝[>] 0) (𝓝 (∫ x in ball Q.z Q.R, Q.cutoffKernel y x * f x ∂D.μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hε₀)] with ε hε
    unfold truncatedIntegral
    exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_ball.measurableSet inter_subset_left (by
      intro x hx
      rw [hcut ε hε x hx.1 (fun hc => hx.2 ⟨hx.1, hc⟩), mul_zero])
  exact tendsto_nhds_unique (Q.principalValue_limit hδ hf hy) ht

end RothschildStein.H2
