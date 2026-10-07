-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.CriticalRegularizedPotentialIdentity
public import RothschildStein.H1.CriticalCutoffErrorBound
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The regularized critical potential has a
uniform Cε error from PV plus the actual cutoff moment. -/
theorem exists_criticalRegularizedPotential_error_bound
    {ν F η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hη : Continuous η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R : ℝ} (hR : 0 < R) (hηout : ∀ w, R ≤ ν w → η w = 0)
    (hbη : ∀ w, ‖η w‖ ≤ 1) (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → R * ε < 1 → ∀ x,
      ‖G2.groupConvolution G ψ (fun w => F w * (1 - η (G.dilate ε⁻¹ w))) x -
        (principalValueConvolution G ν F ψ x + ψ x * (∫ v in {v | ν v ≤ R}, F v * (1 - η v)))‖ ≤ C * ε := by
  obtain ⟨C, hC, hb⟩ := exists_criticalKernel_weightedSmallBall_bound G hν hF hhom hcψ hsψ
  refine ⟨C * R, mul_nonneg hC hR.le, ?_⟩
  intro ε hε hRε x
  rw [criticalRegularizedPotential_eq_PV_moment_sub_error G hν hF hhom hcancel hη heη hR hε hRε hηout hcψ hsψ x]
  let A := principalValueConvolution G ν F ψ x + ψ x * (∫ v in {v | ν v ≤ R}, F v * (1 - η v))
  let E := ∫ w in {w | ν w ≤ R * ε}, η (G.dilate ε⁻¹ w) * (F w * (ψ (G.mul x (G.inv w)) - ψ x))
  change ‖(A - E) - A‖ ≤ (C * R) * ε
  have he : (A - E) - A = -E := by ring
  rw [he, norm_neg]
  exact (hb (R * ε) (mul_pos hR hε) hRε.le (fun w => η (G.dilate ε⁻¹ w))
    (fun w => hbη _) x).trans_eq (by ring)

/-- Smooth cutoff regularization of the
critical kernel converges uniformly to PV plus its scalar cutoff
moment, with every term given by actual convergent integrals. -/
theorem tendstoUniformly_criticalRegularizedPotential
    {ν F η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hη : Continuous η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R : ℝ} (hR : 0 < R) (hηout : ∀ w, R ≤ ν w → η w = 0)
    (hbη : ∀ w, ‖η w‖ ≤ 1) (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) :
    TendstoUniformly (fun ε => G2.groupConvolution G ψ (fun w => F w * (1 - η (G.dilate ε⁻¹ w))))
      (fun x => principalValueConvolution G ν F ψ x + ψ x * (∫ v in {v | ν v ≤ R}, F v * (1 - η v)))
      (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨C, hC, hb⟩ := exists_criticalRegularizedPotential_error_bound G hν hF hhom hcancel hη heη hR hηout hbη hcψ hsψ
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => C * ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hid
  have hRt : Tendsto (fun ε : ℝ => R * ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hid
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, hRt.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    ht.eventually (gt_mem_nhds hδ)] with ε hε hRε he
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (hb ε hε hRε x).trans_lt he

end RothschildStein.H1
