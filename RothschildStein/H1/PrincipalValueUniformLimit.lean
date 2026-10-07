-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueErrorBound
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Critical cancelled kernels have principal-value
convolution limits uniformly on the entire group. -/
theorem tendstoUniformly_principalValueTruncation
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    TendstoUniformly (principalValueTruncation G ν F ψ)
      (principalValueConvolution G ν F ψ) (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨C, hC, hb⟩ := exists_principalValue_uniform_error_bound G hν hF hhom hcancel hc hs
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), C * ε < η := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      have hi : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hi)
    exact ht.eventually (gt_mem_nhds hη)
  have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hsmall, hbound] with ε hε hε1 he
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (hb ε hε hε1 x).trans_lt he

end RothschildStein.H1
