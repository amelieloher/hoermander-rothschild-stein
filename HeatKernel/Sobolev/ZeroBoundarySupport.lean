-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryCore
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! # Almost everywhere support of zero-boundary form functions -/

@[expose] public section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace HeatKernel.Sobolev

/-- A zero-boundary graph function vanishes almost everywhere outside its domain. -/
theorem ae_eq_zero_outside_of_mem_zeroBoundaryGraph {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (v : zeroBoundaryGraph U X) :
    ∀ᵐ x ∂volume, x ∉ (U : Set (Fin N → ℝ)) →
      (v : GradientSpace (N := N) ⊤ q).fst x = 0 := by
  obtain ⟨w, hw, ht⟩ := exists_interiorGradientPairs_tendsto U X v
  choose f hf hc hs hrep hg using hw
  have hfirst := ((tendsto_GradientSpace_iff ⊤).mp ht).1
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfirst).exists_seq_tendsto_ae
  simp only [Opens.coe_top, Measure.restrict_univ] at hae
  have hreps : ∀ᵐ x ∂volume, ∀ n : ℕ, (w (ns n)).fst x = f (ns n) x :=
    ae_all_iff.mpr (fun n => hrep (ns n))
  filter_upwards [hae, hreps] with x hx hfx
  intro houtside
  have hz (n : ℕ) : (w (ns n)).fst x = 0 := by
    rw [hfx n]
    exact image_eq_zero_of_notMem_tsupport (fun h => houtside (hs (ns n) h))
  have hzero : Tendsto (fun n => (w (ns n)).fst x) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hx hzero

end HeatKernel.Sobolev
