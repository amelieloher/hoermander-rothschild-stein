-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Smooth compactly supported cutoffs on finite-dimensional real vector spaces. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology BigOperators

namespace HeatKernel

/-- A finite family of nonnegative smooth bumps covering a compact set can be saturated
into a smooth plateau without enlarging its support. -/
theorem exists_smooth_cutoff_of_finite_cover {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : Finset ι) (f : ι → E → ℝ) (C U : Set E)
    (hf : ∀ i ∈ t, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hc : ∀ i ∈ t, HasCompactSupport (f i))
    (hu : ∀ i ∈ t, tsupport (f i) ⊆ U)
    (hn : ∀ i ∈ t, ∀ x, 0 ≤ f i x)
    (hcover : ∀ x ∈ C, ∃ i ∈ t, (1 : ℝ) / 2 < f i x) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, χ x ∈ Icc 0 1) ∧ ∀ x ∈ C, χ x = 1 := by
  classical
  let S : E → ℝ := fun x => ∑ i ∈ t, f i x
  let H : ℝ → ℝ := fun z => Real.smoothTransition (4 * z - 1)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hHzero : H 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hS : ContDiff ℝ (⊤ : ℕ∞) S := ContDiff.sum hf
  have hK : IsCompact (⋃ i ∈ t, tsupport (f i)) := t.isCompact_biUnion hc
  have hsub : tsupport S ⊆ ⋃ i ∈ t, tsupport (f i) := by
    apply hK.isClosed.closure_subset_iff.mpr
    intro x hx
    by_contra h
    have hz : ∀ i ∈ t, f i x = 0 := by
      intro i hi
      apply image_eq_zero_of_notMem_tsupport
      exact fun hm => h (mem_iUnion_of_mem i (mem_iUnion_of_mem hi hm))
    exact hx (Finset.sum_eq_zero hz)
  have hSc : HasCompactSupport S := hK.of_isClosed_subset (isClosed_tsupport S) hsub
  refine ⟨H ∘ S, hH.comp hS, hSc.comp_left hHzero, ?_, ?_, ?_⟩
  · exact (tsupport_comp_subset hHzero S).trans (hsub.trans (by
      intro x hx
      rcases mem_iUnion₂.mp hx with ⟨i, hi, hx⟩
      exact hu i hi hx))
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := hcover x hx
    have hle : f i x ≤ S x := Finset.single_le_sum (fun j hj => hn j hj x) hi
    apply Real.smoothTransition.one_of_one_le
    dsimp [S] at hle ⊢
    linarith

/-- A compact set in an open set has a smooth compactly supported cutoff equal to one
on the compact set and taking values in the unit interval. -/
theorem exists_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C U : Set E} (hC : IsCompact C) (hU : IsOpen U)
    (hCU : C ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, χ x ∈ Icc 0 1) ∧ ∀ x ∈ C, χ x = 1 := by
  classical
  have hp : ∀ x : C, ∃ f : E → ℝ, tsupport f ⊆ U ∧ HasCompactSupport f ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 :=
    fun x => exists_contDiff_tsupport_subset (hU.mem_nhds (hCU x.property))
  choose f hfu hfc hfd hfr hfx using hp
  let V : C → Set E := fun x => {y | (1 : ℝ) / 2 < f x y}
  have hVo : ∀ x, IsOpen (V x) := fun x => isOpen_lt continuous_const (hfd x).continuous
  have hcov : C ⊆ ⋃ x : C, V x := by
    intro x hx
    apply mem_iUnion_of_mem (⟨x, hx⟩ : C)
    change (1 : ℝ) / 2 < f ⟨x, hx⟩ x
    rw [hfx]
    norm_num
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo hcov
  apply exists_smooth_cutoff_of_finite_cover t f C U
  · exact fun i _ => hfd i
  · exact fun i _ => hfc i
  · exact fun i _ => hfu i
  · exact fun i _ x => (hfr i (mem_range_self x)).1
  · intro x hx
    rcases mem_iUnion₂.mp (ht hx) with ⟨i, hi, hix⟩
    exact ⟨i, hi, hix⟩

end HeatKernel
