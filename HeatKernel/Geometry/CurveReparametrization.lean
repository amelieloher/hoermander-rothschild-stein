-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Order.Interval.Set.Disjoint

/-! Absolute continuity under monotone Lipschitz changes of parameter. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
open scoped BigOperators NNReal

namespace HeatKernel

private theorem disjWithin_comp {g : ℝ → ℝ} {a b c d : ℝ}
    (hg : Monotone g ∨ Antitone g) (hm : MapsTo g (uIcc a b) (uIcc c d))
    {E : ℕ × (ℕ → ℝ × ℝ)} (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    (E.1, fun i => (g (E.2 i).1, g (E.2 i).2)) ∈
      AbsolutelyContinuousOnInterval.disjWithin c d := by
  refine ⟨fun i hi => ⟨hm (hE.1 i hi).1, hm (hE.1 i hi).2⟩, ?_⟩
  intro i hi j hj hij
  have h := hE.2 hi hj hij
  simp only [uIoc, Ioc_disjoint_Ioc] at h ⊢
  rcases hg with hg | hg
  · simpa only [hg.map_min, hg.map_max] using hg h
  · simpa only [hg.map_min, hg.map_max] using hg h

/-- An absolutely continuous curve remains absolutely continuous after a monotone or
antitone Lipschitz change of parameter whose image stays in the original interval. -/
theorem absolutelyContinuousOnInterval_comp_of_monotone {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {g : ℝ → ℝ} {a b c d : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f c d) (hg : Monotone g ∨ Antitone g)
    (hK : LipschitzOnWith K g (uIcc a b)) (hm : MapsTo g (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ / (K + 1), div_pos hδ (by positivity), fun A hA hsmall => ?_⟩
  let B : ℕ × (ℕ → ℝ × ℝ) := (A.1, fun i => (g (A.2 i).1, g (A.2 i).2))
  have hB : B ∈ AbsolutelyContinuousOnInterval.disjWithin c d := disjWithin_comp hg hm hA
  have hsum : ∑ i ∈ Finset.range B.1, dist (B.2 i).1 (B.2 i).2 ≤
      K * ∑ i ∈ Finset.range A.1, dist (A.2 i).1 (A.2 i).2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      hK.dist_le_mul _ (hA.1 i hi).1 _ (hA.1 i hi).2
  have hlt : K * ∑ i ∈ Finset.range A.1, dist (A.2 i).1 (A.2 i).2 < δ := by
    have hpos : 0 < (K : ℝ) + 1 := by positivity
    have hnonneg := Finset.sum_nonneg (s := Finset.range A.1)
      (fun i _ => dist_nonneg (x := (A.2 i).1) (y := (A.2 i).2))
    have hh := (lt_div_iff₀ hpos).mp hsmall
    nlinarith
  exact hbound B hB (hsum.trans_lt hlt)

end HeatKernel
