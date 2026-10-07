-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.FieldHomogeneity
public import RothschildStein.G2.HomogeneousDivergence
public import RothschildStein.G1.ParameterFlows

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The prescribed tangent parameter and spatial point give
a jointly smooth family of left-invariant fields (BB pp. 108, 117–118). -/
theorem contDiff_leftField_parameters :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : (Fin N → ℝ) × (Fin N → ℝ) => leftField G q.1 q.2) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin N → ℝ => fderiv ℝ (G.mul x) 0) :=
    (contDiff_mul G).fderiv (g := fun _ => (0 : Fin N → ℝ)) contDiff_const (by simp)
  exact (hd.comp contDiff_snd).clm_apply contDiff_fst

theorem dilate_smul (l c : ℝ) (v : Fin N → ℝ) :
    G.dilate l (c • v) = c • G.dilate l v :=
  (dilationDifferential G l).map_smul c v

/-- Positive dilations put any tangent vector into any prescribed
open parameter ball, even after a fixed positive time rescaling. -/
theorem exists_small_dilated_parameter (v : Fin N → ℝ) {c r : ℝ} (hr : 0 < r) :
    ∃ l : ℝ, 0 < l ∧ ‖c • G.dilate l v‖ < r := by
  have hc : ContinuousAt (fun l : ℝ => c • G.dilate l v) 0 :=
    (continuousAt_dilate_parameter_zero G v).const_smul c
  have hn : ∀ᶠ l : ℝ in 𝓝 0, ‖c • G.dilate l v‖ < r :=
    hc.norm.eventually_lt continuousAt_const (by rw [zero_dilate,smul_zero,norm_zero]; exact hr)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε/2,half_pos hε,hball ?_⟩
  rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
  exact half_lt_self hε

end RothschildStein.G2
