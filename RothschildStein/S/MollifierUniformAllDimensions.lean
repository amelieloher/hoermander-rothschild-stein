-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierUniformBounded
public import RothschildStein.S.MollifierAllDimensions
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Continuous compactly supported functions are
approximated uniformly by ordinary mollifiers in every coordinate
dimension (BB Lemma 2.8, p. 72 and Thm 2.20, p. 86). -/
theorem tendstoUniformly_euclideanRegularize_compact_all_dimensions
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun ε : ℝ => euclideanRegularize n f ε) f (𝓝[>] 0) := by
  by_cases hn : n = 0
  · subst n
    apply Metric.tendstoUniformly_iff.mpr
    intro η hη
    exact Eventually.of_forall (fun ε x => by
      simpa only [euclideanRegularize_zero_dimension,dist_self] using hη)
  · obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
    exact tendstoUniformly_euclideanRegularize_of_uniformContinuous (Nat.pos_of_ne_zero hn)
      (hc.uniformContinuous_of_continuous hf) hC

end RothschildStein.S
