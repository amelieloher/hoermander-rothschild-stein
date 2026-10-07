-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.G2.Gauge
public import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- an actual compact smooth cutoff with all properties
needed by the homogeneous potential regularization. -/
theorem exists_compactGaugeCutoff {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    ∃ η : (Fin N → ℝ) → ℝ, ∃ R : ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      η =ᶠ[𝓝 (0 : Fin N → ℝ)] (fun _ => 1) ∧ 0 < R ∧
      (∀ w, R ≤ ν w → η w = 0) ∧ (∀ w, ‖η w‖ ≤ 1) := by
  let U : Opens (Fin N → ℝ) := ⟨univ, isOpen_univ⟩
  obtain ⟨η, W, hW, hKW, hOne, hRange⟩ := exists_test_eq_one_near_compact U
    (isCompact_singleton (x := (0 : Fin N → ℝ))) (subset_univ _)
  obtain ⟨B, hB⟩ := η.hasCompactSupport.isCompact.exists_bound_of_continuousOn hν.1.continuousOn
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right B 0]
  refine ⟨η, R, η.contDiff, η.hasCompactSupport, ?_, hR, ?_, ?_⟩
  · filter_upwards [hW.mem_nhds (hKW (mem_singleton 0))] with w hw
    exact hOne w hw
  · intro w hw
    by_contra hn
    have hs : w ∈ tsupport (η : (Fin N → ℝ) → ℝ) := subset_closure hn
    have hb := hB w hs
    have hpos := hν.2.1 w
    dsimp [R] at hw
    rw [Real.norm_of_nonneg hpos] at hb
    linarith [le_max_left B 0]
  · intro w
    rw [Real.norm_of_nonneg (hRange w).1]
    exact (hRange w).2

end RothschildStein.H1
