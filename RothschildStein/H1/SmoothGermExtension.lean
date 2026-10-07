-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.Definitions.testMultiplierOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- A locally smooth function has a globally smooth compact
representative of its germ at any interior point. -/
theorem exists_smoothCompact_germ (U : Opens (Fin N → ℝ))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (U : Set (Fin N → ℝ)))
    {x : Fin N → ℝ} (hx : x ∈ U) :
    ∃ g : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      g =ᶠ[𝓝 x] f := by
  obtain ⟨η, W, hW, hxW, he, _⟩ :=
    exists_test_eq_one_near_compact U isCompact_singleton (singleton_subset_iff.mpr hx)
  let g := testMultiplierOn U f hf η
  refine ⟨g, g.contDiff, g.hasCompactSupport, ?_⟩
  filter_upwards [hW.mem_nhds (hxW (mem_singleton x))] with y hy
  change η y * f y = f y
  rw [he y hy, one_mul]

end RothschildStein.H1
