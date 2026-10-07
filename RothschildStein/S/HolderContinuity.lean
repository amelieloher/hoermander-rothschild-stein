-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds
public import RothschildStein.S.DistanceMetricLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Finiteness of the Hölder norm gives Euclidean
continuity on any subset of the ambient domain. Only finite-distance
pairs sufficiently near the base point are needed (BB Def 2.13,
p. 81; Thm 1.53, p. 35). -/
theorem continuousOn_of_holderENorm_lt_top_on_subset
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    {V : Set (Fin n → ℝ)} (hV : V ⊆ Ω) {α : ℝ} (hα : 0 < α)
    {f : (Fin n → ℝ) → ℝ} (hf : holderENorm G.d α V f < ⊤) :
    ContinuousOn f V := by
  let S := holderSeminorm G.d α V f
  have hs : S < ⊤ := lt_of_le_of_lt le_add_self hf
  intro x hx
  apply tendsto_iff_edist_tendsto_0.mpr
  have hxx : G.d x x = 0 := (G.distance_eq_zero_iff ⟨x,hV hx⟩ ⟨x,hV hx⟩).mpr rfl
  have hd : Tendsto (G.d x) (𝓝[V] x) (𝓝 0) := by
    simpa only [ContinuousWithinAt,hxx] using ((G.continuousOn_distance ⟨x,hV hx⟩).mono hV x hx)
  have ht := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hs.ne hα).comp hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [self_mem_nhdsWithin,hd.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ⊤ from bot_lt_top))]
      with y hy hdy
    have hsep : ∀ a ∈ V, ∀ b ∈ V, G.d a b = 0 → a = b := by
      intro a ha b hb hab
      exact congrArg Subtype.val ((G.distance_eq_zero_iff ⟨a,hV ha⟩ ⟨b,hV hb⟩).mp hab)
    simpa only [edist_dist,Real.dist_eq,abs_sub_comm,Function.comp_def,S] using!
      holderSeminorm_increment_le G.d α V f hα hsep hx hy hdy

end RothschildStein.S
