-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.L1

/-- Uniqueness makes a supplied inverse on an open target jointly
smooth. No continuity assumption on the supplied inverse is needed; local
inverse function theorems agree by source injectivity (BB pp. 520–521). -/
theorem contDiffOn_chart_inverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (f : E → F) (g : F → E) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hinj : InjOn f U) (hg : MapsTo g V U)
    (hfg : ∀ y ∈ V, f (g y) = y)
    (hderiv : ∀ x ∈ U, ∃ L : E ≃L[ℝ] F, HasFDerivAt f (L : E →L[ℝ] F) x) :
    ContDiffOn ℝ (⊤ : ℕ∞) g V := by
  intro y hy
  have hx := hg hy
  have hfa := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨L, hL⟩ := hderiv (g y) hx
  have hs := hfa.hasStrictFDerivAt' hL (by simp)
  have hv : ∀ᶠ x in 𝓝 (g y), f x ∈ V := by
    apply hfa.continuousAt.preimage_mem_nhds
    rw [hfg y hy]
    exact hV.mem_nhds hy
  have hleft : ∀ᶠ x in 𝓝 (g y), g (f x) = x := by
    filter_upwards [hU.mem_nhds hx, hv] with x hx hxV
    exact hinj (hg hxV) hx (hfg (f x) hxV)
  have huniq := hs.localInverse_unique hleft
  have hlocal := hfa.to_localInverse hL (by simp)
  have hresult : ContDiffAt ℝ (⊤ : ℕ∞) g (f (g y)) :=
    hlocal.congr_of_eventuallyEq huniq
  rw [hfg y hy] at hresult
  exact hresult.contDiffWithinAt

end RothschildStein.L1
