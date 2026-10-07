-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.rsBall
public import RothschildStein.G1.LocalDisplacement
public import RothschildStein.G1.CompactClosedControlBalls
public import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators ENNReal
namespace RothschildStein.G1

/-- Compactness supplies a uniform Euclidean interior buffer
and field bound (BB Thm 1.53, pp. 35–36). -/
theorem exists_uniform_control_buffer {m n : ℕ}
    {Ω K V : Set (Fin n → ℝ)} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVΩ : V ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) :
    ∃ B R : ℝ, 0 < B ∧ 0 < R ∧
      (∀ x ∈ K, closedBall x R ⊆ V) ∧
      (∀ x ∈ K, ∀ z, ‖z-x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) := by
  obtain ⟨R,hR,hRV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hc : ContinuousOn (fun z => ∑ i, ‖X i z‖) (cthickening R K) :=
    continuousOn_finsetSum _ (fun i _ => ((hX i).mono (hRV.trans hVΩ)).norm)
  obtain ⟨B,hbound⟩ := ((hK.cthickening).image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max 1 B,R,zero_lt_one.trans_le (le_max_left _ _),hR,?_,?_⟩
  · intro x hx z hz
    exact hRV (mem_cthickening_of_dist_le z x R K hx hz)
  · intro x hx z hz
    have hb := hbound _ (mem_image_of_mem _ (mem_cthickening_of_dist_le z x R K hx
      (by simpa only [dist_eq_norm] using hz)))
    exact (le_abs_self _).trans (hb.trans (le_max_right _ _))

end RothschildStein.G1
