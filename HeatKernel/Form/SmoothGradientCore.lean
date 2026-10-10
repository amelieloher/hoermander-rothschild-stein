-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoreGradientGraph
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Sequences

/-!
# Smooth representatives of the gradient core

Smooth compact gradient pairs form a linear subspace. Thus every vector in their span still
has a single smooth compact representative, and every energy-domain vector is a graph-norm
limit of such pairs.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal Topology

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Field differentiation is additive on smooth functions. -/
theorem fieldDerivative_add_contDiff {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    fieldDerivative V (f + g) = fieldDerivative V f + fieldDerivative V g := by
  funext x
  simp only [fieldDerivative, fderiv_add ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt), add_apply, Pi.add_apply]

/-- Field differentiation commutes with constant scalar multiplication on smooth functions. -/
theorem fieldDerivative_smul_contDiff {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) :
    fieldDerivative V (c • f) = c • fieldDerivative V f := by
  funext x
  simp only [fieldDerivative, fderiv_const_smul ((hf.differentiable (by simp)).differentiableAt),
    smul_apply, Pi.smul_apply]

/-- The sum of two smooth compact gradient pairs has a smooth compact representative. -/
theorem add_mem_smoothGradientPairs {v w : GradientSpace U q}
    (hv : v ∈ smoothGradientPairs U X) (hw : w ∈ smoothGradientPairs U X) :
    v + w ∈ smoothGradientPairs U X := by
  obtain ⟨f, hf, hc, hs, hvf, hvg⟩ := hv
  obtain ⟨g, hg, hgc, hgs, hwg, hwgrad⟩ := hw
  refine ⟨f + g, hf.add hg, hc.add hgc, (tsupport_add f g).trans (union_subset hs hgs),
    (Lp.coeFn_add v.fst w.fst).trans (hvf.add hwg), fun i => ?_⟩
  rw [fieldDerivative_add_contDiff hf hg]
  exact (Lp.coeFn_add (v.snd i) (w.snd i)).trans ((hvg i).add (hwgrad i))

/-- A constant multiple of a smooth compact gradient pair has a smooth compact representative. -/
theorem smul_mem_smoothGradientPairs {v : GradientSpace U q}
    (hv : v ∈ smoothGradientPairs U X) (c : ℝ) : c • v ∈ smoothGradientPairs U X := by
  obtain ⟨f, hf, hc, hs, hvf, hvg⟩ := hv
  refine ⟨c • f, hf.const_smul c, hc.smul_left,
    (tsupport_smul_subset_right (fun _ => c) f).trans hs,
    (Lp.coeFn_smul c v.fst).trans (hvf.fun_comp (c • ·)), fun i => ?_⟩
  rw [fieldDerivative_smul_contDiff hf c]
  exact (Lp.coeFn_smul c (v.snd i)).trans ((hvg i).fun_comp (c • ·))

/-- The zero vector is a smooth compact gradient pair. -/
theorem zero_mem_smoothGradientPairs : (0 : GradientSpace U q) ∈ smoothGradientPairs U X := by
  refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, Lp.coeFn_zero _ _ _, fun i => ?_⟩
  have hz : fieldDerivative (X i) (0 : (Fin N → ℝ) → ℝ) = 0 := by
    funext x
    simp only [fieldDerivative, Pi.zero_def, fderiv_const_apply, zero_apply]
  rw [hz]
  exact Lp.coeFn_zero _ _ _

/-- The linear span of the smooth gradient pairs contains exactly those pairs. -/
theorem mem_smoothGradientSpan_iff {v : GradientSpace U q} :
    v ∈ smoothGradientSpan U X ↔ v ∈ smoothGradientPairs U X := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => exact zero_mem_smoothGradientPairs U X
    | add v w _ _ hv hw => exact add_mem_smoothGradientPairs U X hv hw
    | smul c v _ hv => exact smul_mem_smoothGradientPairs U X hv c
  · intro hv
    exact Submodule.subset_span hv

/-- Every energy-domain vector is a graph-norm limit of smooth compact gradient pairs. -/
theorem exists_smoothGradientPairs_tendsto (v : energyGraph U X) :
    ∃ w : ℕ → GradientSpace U q, (∀ n, w n ∈ smoothGradientPairs U X) ∧
      Tendsto w atTop (𝓝 (v : GradientSpace U q)) := by
  obtain ⟨w, hw, ht⟩ := mem_closure_iff_seq_limit.mp v.property
  exact ⟨w, fun n => (mem_smoothGradientSpan_iff U X).mp (hw n), ht⟩

end HeatKernel
