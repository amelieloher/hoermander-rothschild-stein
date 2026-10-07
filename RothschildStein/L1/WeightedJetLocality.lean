-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PartialJetCoordinates
public import RothschildStein.S.WordDerivativeGerms
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Ordered coordinate jets depend only on the actual local germ. -/
theorem rsPartial_eventuallyEq {N : ℕ} (J : List (Fin N))
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (he : f =ᶠ[𝓝 x] g) :
    rsPartial J f =ᶠ[𝓝 x] rsPartial J g := by
  simp only [rsPartial_eq_constant_wordDerivative]
  exact S.wordDerivative_eventuallyEq _ J he

/-- Weighted jet classes transfer across equality on the original open domain. -/
theorem scalarJetClass_congr {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : scalarJetClass Ω ω a p f)
    (he : EqOn g f Ω) : scalarJetClass Ω ω a p g := by
  refine ⟨hf.1.congr he, ?_⟩
  have hg : g =ᶠ[𝓝 (0 : Fin N → ℝ)] f :=
    Filter.Eventually.mono (Ω.isOpen.mem_nhds h0) (fun y hy => he hy)
  intro J hJ hw
  rw [(rsPartial_eventuallyEq J hg).self_of_nhds]
  exact hf.2 J hJ hw
end RothschildStein.L1
