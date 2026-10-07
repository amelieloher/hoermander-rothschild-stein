-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.SmoothChartInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.L1

/-- Source injectivity and the actual inverse identities give
the derivative of the chosen chart inverse, without a continuity premise
on that inverse (BB pp. 520–521). -/
theorem hasFDerivAt_chart_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (f : E → F) (g : F → E) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hinj : InjOn f U) (hg : MapsTo g V U) (hfg : ∀ y ∈ V, f (g y) = y)
    {y : F} (hy : y ∈ V) (L : E ≃L[ℝ] F)
    (hL : HasFDerivAt f (L : E →L[ℝ] F) (g y)) :
    HasFDerivAt g (L.symm : F →L[ℝ] E) y := by
  have hx := hg hy
  have hfa := hf.contDiffAt (hU.mem_nhds hx)
  have hs := hfa.hasStrictFDerivAt' hL (by simp)
  have hv : ∀ᶠ x in 𝓝 (g y), f x ∈ V := by
    apply hfa.continuousAt.preimage_mem_nhds
    rw [hfg y hy]
    exact hV.mem_nhds hy
  have hleft : ∀ᶠ x in 𝓝 (g y), g (f x) = x := by
    filter_upwards [hU.mem_nhds hx, hv] with x hx hxV
    exact hinj (hg hxV) hx (hfg (f x) hxV)
  have hh := (hs.to_local_left_inverse hleft).hasFDerivAt
  rw [hfg y hy] at hh
  exact hh

end RothschildStein.L1
