-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.ZeroBoundaryFirstMoment
public import HeatKernel.Sobolev.LevelTruncationForm
import Mathlib.Tactic

/-! # Measurable supported representatives and their level truncations -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal
namespace HeatKernel.Sobolev

/-- Zero-boundary graph elements have measurable representatives supported inside the domain. -/
theorem exists_measurable_supported_zeroBoundaryGraph_rep {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : zeroBoundaryGraph U X) :
    ∃ f : (Fin N → ℝ) → ℝ, Measurable f ∧ Function.support f ⊆ (U : Set (Fin N → ℝ)) ∧
      (v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f ∧ MemLp f 2 volume := by
  have hf : MemLp (v : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst)
  let hmeas := hf.aestronglyMeasurable
  let f := (U : Set (Fin N → ℝ)).indicator (hmeas.mk (v : GradientSpace (N := N) ⊤ q).fst)
  have hfm : Measurable f := hmeas.measurable_mk.indicator U.isOpen.measurableSet
  have hs : Function.support f ⊆ (U : Set (Fin N → ℝ)) := by
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  have heq : (v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f := by
    filter_upwards [hmeas.ae_eq_mk, ae_eq_zero_outside_of_mem_zeroBoundaryGraph U X v] with x hx hz
    by_cases hmem : x ∈ (U : Set (Fin N → ℝ))
    · simpa only [f, indicator_of_mem hmem] using hx
    · simpa only [f, indicator_of_notMem hmem] using hz hmem
  exact ⟨f, hfm, hs, heq, (memLp_congr_ae heq).mp hf⟩

end HeatKernel.Sobolev
