-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.AffineAbsoluteContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal

namespace RothschildStein.G1

/-- Monotone Lipschitz time changes preserve absolute continuity, even
when some subintervals collapse (BB Prop 1.36, p. 19). -/
theorem absolutelyContinuousOnInterval_comp_monotone {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {g : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0}
    (hg : Monotone g) (hK : LipschitzWith K g)
    (hf : AbsolutelyContinuousOnInterval f (g a) (g b)) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ / (K + 1), by positivity, ?_⟩
  intro E hE hsmall
  have hdisj : (E.1, fun i => (g (E.2 i).1, g (E.2 i).2)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (g a) (g b) := by
    refine ⟨fun i hi => ⟨hg.image_uIcc_subset (mem_image_of_mem g (hE.1 i hi).1),
      hg.image_uIcc_subset (mem_image_of_mem g (hE.1 i hi).2)⟩, ?_⟩
    intro i hi j hj hij
    have hh := hE.2 hi hj hij
    simp only [uIoc, Ioc_disjoint_Ioc] at hh ⊢
    simpa only [hg.map_min, hg.map_max] using hg hh
  apply hbound _ hdisj
  calc
    ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) ≤
        ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (E.2 i).1 (E.2 i).2 :=
      Finset.sum_le_sum (fun i _ => hK.dist_le_mul _ _)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ((K : ℝ) + 1) * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
      gcongr; linarith
    _ < δ := by
      simpa only [mul_comm] using (lt_div_iff₀ (by positivity : (0 : ℝ) < K + 1)).mp hsmall

/-- Absolute continuity glues across a common endpoint. This supplies
piecewise absolute continuity in the weighted concatenation proof
(BB Prop 1.36, p. 19). -/
theorem absolutelyContinuousOnInterval_glue {F : Type*} [SeminormedAddCommGroup F]
    {f : ℝ → F} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval f b c) :
    AbsolutelyContinuousOnInterval f a c := by
  have hleft : AbsolutelyContinuousOnInterval (fun t => f (min t b)) a c := by
    have hh := absolutelyContinuousOnInterval_comp_monotone
      (monotone_id.min (monotone_const : Monotone (fun _ : ℝ => b))) (LipschitzWith.id.min_const b)
      (a := a) (b := c) (f := f)
    simpa only [id_eq, min_eq_left hab, min_eq_right hbc, Function.comp_def] using hh
      (by simpa only [id_eq, min_eq_left hab, min_eq_right hbc] using hf)
  have hright : AbsolutelyContinuousOnInterval (fun t => f (max t b)) a c := by
    have hh := absolutelyContinuousOnInterval_comp_monotone
      (monotone_id.max (monotone_const : Monotone (fun _ : ℝ => b))) (LipschitzWith.id.max_const b)
      (a := a) (b := c) (f := f)
    simpa only [id_eq, max_eq_right hab, max_eq_left hbc, Function.comp_def] using hh
      (by simpa only [id_eq, max_eq_right hab, max_eq_left hbc] using hg)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f b) a c :=
    (LipschitzWith.const (f b)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply ((hleft.add hright).sub hconst).congr
  intro t _ht
  simp only [Pi.sub_apply, Pi.add_apply]
  rcases le_total t b with h | h
  · simp only [min_eq_left h, max_eq_right h, add_sub_cancel_right]
  · simp only [min_eq_right h, max_eq_left h]
    abel

end RothschildStein.G1
