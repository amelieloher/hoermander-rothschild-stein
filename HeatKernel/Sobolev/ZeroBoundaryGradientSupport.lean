-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryCore
public import RothschildStein.S.ClassicalWords
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! # Almost everywhere support of zero-boundary horizontal gradients -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology
namespace HeatKernel.Sobolev

/-- Every component of a zero-boundary horizontal gradient vanishes outside its domain. -/
theorem ae_eq_zero_gradient_outside_of_mem_zeroBoundaryGraph {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : zeroBoundaryGraph U X) (i : Fin q) :
    ∀ᵐ x ∂volume, x ∉ (U : Set (Fin N → ℝ)) →
      (v : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
  obtain ⟨w, hw, ht⟩ := exists_interiorGradientPairs_tendsto U X v
  choose f hf hc hs hrep hg using hw
  have hfirst := ((tendsto_GradientSpace_iff ⊤).mp ht).2 i
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae
  simp only [Opens.coe_top, Measure.restrict_univ] at hae
  have hreps : ∀ᵐ x ∂volume, ∀ n : ℕ, (w (ns n)).snd i x = fieldDerivative (X i) (f (ns n)) x :=
    ae_all_iff.mpr (fun n => hg (ns n) i)
  filter_upwards [hae, hreps] with x hx hfx
  intro houtside
  have hz (n : ℕ) : (w (ns n)).snd i x = 0 := by
    rw [hfx n]
    exact image_eq_zero_of_notMem_tsupport
      (fun h => houtside (hs (ns n) (S.tsupport_fieldDerivative_subset (X i) (f (ns n)) h)))
  have hzero : Tendsto (fun n => (w (ns n)).snd i x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hx hzero

end HeatKernel.Sobolev
