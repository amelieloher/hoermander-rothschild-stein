-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RegularizedPotentialErrorBound
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 2: cutoff regularization of a homogeneous
potential above degree −Q converges uniformly on the whole group. -/
theorem tendstoUniformly_regularizedPotential
    {ν f η ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ) {β : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : -(G.homogeneousDimension : ℝ) < β)
    (hη : Continuous η) {R : ℝ} (hR : 0 < R)
    (hηout : ∀ w, R ≤ ν w → η w = 0) (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) :
    TendstoUniformly (fun ε => G2.groupConvolution G ψ (fun w => f w * (1 - η (G.dilate ε⁻¹ w))))
      (G2.groupConvolution G ψ f) (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨C, hC, hb⟩ := exists_regularizedPotential_error_bound G hν hf hhom hβ hη hR hηout hbη hcψ hsψ
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hRt : Tendsto (fun ε : ℝ => R * ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hid
  have hp : 0 < (G.homogeneousDimension : ℝ) + β := by linarith
  have ht : Tendsto (fun ε : ℝ => C * (R * ε) ^ ((G.homogeneousDimension : ℝ) + β))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (hRt.rpow_const_nhds_zero hp)
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hδ)] with ε hε he
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (hb ε hε x).trans_lt he

end RothschildStein.H1
