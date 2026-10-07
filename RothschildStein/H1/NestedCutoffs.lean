-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- A smooth interior cutoff equals one on an open neighborhood
of any prescribed compact subset (BB p. 265). -/
theorem exists_test_eq_one_near_compact (Ω : Opens (Fin N → ℝ))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ η : TestFunction Ω ℝ (⊤ : ℕ∞), ∃ W : Set (Fin N → ℝ),
      IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, η x = 1) ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) := by
  obtain ⟨W, hW, hKW, hclW, hcW⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  obtain ⟨V, hV, hWV, hclV, hcV⟩ :=
    exists_open_between_and_isCompact_closure hcW Ω.isOpen hclW
  obtain ⟨f, hd, hrange, hs, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  have hts : tsupport f ⊆ (Ω : Set (Fin N → ℝ)) := by rw [tsupport, hs]; exact hclV
  let η : TestFunction Ω ℝ (⊤ : ℕ∞) :=
    ⟨f, hd, by simpa only [HasCompactSupport, tsupport, hs] using hcV, hts⟩
  refine ⟨η, W, hW, hKW, ?_, ?_⟩
  · intro x hx
    exact (hone x).mp (subset_closure hx)
  · intro x
    exact hrange (mem_range_self x)

/-- The two actual compact tests satisfy the nested cutoff
conditions, including equality to one near zero and near the inner support
(BB p. 265). -/
theorem exists_nestedKernelCutoffs (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω) :
    ∃ η₁ η₂ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (η₂ : (Fin N → ℝ) → ℝ) =ᶠ[𝓝 (0 : Fin N → ℝ)] 1 ∧
      (∀ x ∈ tsupport (η₂ : (Fin N → ℝ) → ℝ), η₁ x = 1) ∧
      (∀ x, 0 ≤ η₁ x ∧ η₁ x ≤ 1) ∧ (∀ x, 0 ≤ η₂ x ∧ η₂ x ≤ 1) := by
  obtain ⟨η₂, W, hW, h0W, he₂, hb₂⟩ :=
    exists_test_eq_one_near_compact Ω isCompact_singleton (singleton_subset_iff.mpr h0)
  obtain ⟨η₁, V, _, hV, he₁, hb₁⟩ :=
    exists_test_eq_one_near_compact Ω η₂.hasCompactSupport η₂.tsupport_subset
  refine ⟨η₁, η₂, ?_, fun x hx => he₁ x (hV hx), hb₁, hb₂⟩
  filter_upwards [hW.mem_nhds (h0W (mem_singleton 0))] with x hx
  exact he₂ x hx

end RothschildStein.H1
