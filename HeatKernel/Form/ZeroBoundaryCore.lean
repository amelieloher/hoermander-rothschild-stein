-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundary
import Mathlib.Tactic.Linter

/-! # Smooth core sequences in zero-boundary domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The sum of two smooth compact gradient pairs has a smooth compact representative. -/
theorem add_mem_interiorGradientPairs {v w : GradientSpace (N := N) ⊤ q}
    (hv : v ∈ interiorGradientPairs U X) (hw : w ∈ interiorGradientPairs U X) :
    v + w ∈ interiorGradientPairs U X := by
  obtain ⟨f, hf, hc, hs, hvf, hvg⟩ := hv
  obtain ⟨g, hg, hgc, hgs, hwg, hwgrad⟩ := hw
  refine ⟨f + g, hf.add hg, hc.add hgc, (tsupport_add f g).trans (union_subset hs hgs), ?_, fun i => ?_⟩
  · have h := Lp.coeFn_add v.fst w.fst
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans (hvf.add hwg)
  · rw [fieldDerivative_add_contDiff hf hg]
    have h := Lp.coeFn_add (v.snd i) (w.snd i)
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans ((hvg i).add (hwgrad i))

/-- A constant multiple of a smooth compact gradient pair has a smooth compact representative. -/
theorem smul_mem_interiorGradientPairs {v : GradientSpace (N := N) ⊤ q}
    (hv : v ∈ interiorGradientPairs U X) (c : ℝ) : c • v ∈ interiorGradientPairs U X := by
  obtain ⟨f, hf, hc, hs, hvf, hvg⟩ := hv
  refine ⟨c • f, hf.const_smul c, hc.smul_left,
    (tsupport_smul_subset_right (fun _ => c) f).trans hs, ?_, fun i => ?_⟩
  · have h := Lp.coeFn_smul c v.fst
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans (hvf.fun_comp (c • ·))
  · rw [fieldDerivative_smul_contDiff hf c]
    have h := Lp.coeFn_smul c (v.snd i)
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans ((hvg i).fun_comp (c • ·))

/-- The zero vector is an interior smooth gradient pair. -/
theorem zero_mem_interiorGradientPairs :
    (0 : GradientSpace (N := N) ⊤ q) ∈ interiorGradientPairs U X := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_, fun i => ?_⟩
  · simpa only [WithLp.zero_fst, WithLp.zero_snd, PiLp.zero_apply, Opens.coe_top, Measure.restrict_univ] using
      (Lp.coeFn_zero ℝ 2 (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))
  · have hz : fieldDerivative (X i) (0 : (Fin N → ℝ) → ℝ) = 0 := by
      funext x
      simp only [fieldDerivative, Pi.zero_def, fderiv_const_apply, zero_apply]
    rw [hz]
    simpa only [WithLp.zero_fst, WithLp.zero_snd, PiLp.zero_apply, Opens.coe_top, Measure.restrict_univ] using
      (Lp.coeFn_zero ℝ 2 (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))

/-- The linear span of the smooth gradient pairs contains exactly those pairs. -/
theorem mem_interiorGradientSpan_iff {v : GradientSpace (N := N) ⊤ q} :
    v ∈ (Submodule.span ℝ (interiorGradientPairs U X)) ↔ v ∈ interiorGradientPairs U X := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact zero_mem_interiorGradientPairs U X
    | add v w _ _ hv hw => exact add_mem_interiorGradientPairs U X hv hw
    | smul c v _ hv => exact smul_mem_interiorGradientPairs U X hv c
  · intro hv
    exact Submodule.subset_span hv

/-- Every zero-boundary vector is a graph-norm limit of smooth compact gradient pairs. -/
theorem exists_interiorGradientPairs_tendsto (v : zeroBoundaryGraph U X) :
    ∃ w : ℕ → GradientSpace (N := N) ⊤ q, (∀ n, w n ∈ interiorGradientPairs U X) ∧
      Tendsto w atTop (𝓝 (v : GradientSpace (N := N) ⊤ q)) := by
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp v.property
  exact ⟨w, fun n => (mem_interiorGradientSpan_iff U X).mp (hw n), ht⟩


end HeatKernel
