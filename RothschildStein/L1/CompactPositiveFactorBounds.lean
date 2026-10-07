-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- Positive continuous factors have positive uniform lower and upper
bounds on every nonempty compact patch. -/
theorem compact_positive_factor_bounds {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) (c : E → ℝ)
    (hc : ContinuousOn c K) (hpos : ∀ η ∈ K, 0 < c η) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ η ∈ K, lo ≤ c η ∧ c η ≤ hi := by
  obtain ⟨ηlo,hηlo,hlo⟩ := hK.exists_isMinOn hne hc
  obtain ⟨ηhi,hηhi,hhi⟩ := hK.exists_isMaxOn hne hc
  exact ⟨c ηlo,c ηhi,hpos ηlo hηlo,hpos ηhi hηhi,
    fun η hη => ⟨hlo hη,hhi hη⟩⟩
end RothschildStein.L1
