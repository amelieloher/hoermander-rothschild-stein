-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Order.Interval.Set.Disjoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- Affine time changes preserve disjoint interval families, for either
orientation (BB Prop 1.36, p. 19). -/
theorem affine_disjWithin {a b c d : ℝ} {E : ℕ × (ℕ → ℝ × ℝ)}
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    (E.1, fun i => (c + d * (E.2 i).1, c + d * (E.2 i).2)) ∈
      AbsolutelyContinuousOnInterval.disjWithin (c + d * a) (c + d * b) := by
  let g := fun v : ℝ => c + d * v
  have hmono : 0 ≤ d → Monotone g := fun hd => fun x y hxy => by dsimp [g]; nlinarith
  have hanti : d ≤ 0 → Antitone g := fun hd => fun x y hxy => by dsimp [g]; nlinarith
  have hmap : ∀ v ∈ uIcc a b, g v ∈ uIcc (g a) (g b) := by
    intro v hv
    rcases le_total 0 d with hd | hd
    · exact (hmono hd).image_uIcc_subset (mem_image_of_mem g hv)
    · exact (hanti hd).image_uIcc_subset (mem_image_of_mem g hv)
  refine ⟨fun i hi => ⟨hmap _ (hE.1 i hi).1, hmap _ (hE.1 i hi).2⟩, ?_⟩
  intro i hi j hj hij
  have h := hE.2 hi hj hij
  simp only [uIoc, Ioc_disjoint_Ioc] at h ⊢
  rcases le_total 0 d with hd | hd
  · have hm := hmono hd
    simpa only [hm.map_min, hm.map_max, g] using hm h
  · have hm := hanti hd
    simpa only [hm.map_min, hm.map_max, g] using hm h

/-- Absolutely continuous curves remain absolutely continuous after
an affine time change, including reversal (BB pp. 18–19, 22). -/
theorem absolutelyContinuousOnInterval_comp_affine {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a b c d : ℝ} (hd : d ≠ 0)
    (hf : AbsolutelyContinuousOnInterval f (c + d * a) (c + d * b)) :
    AbsolutelyContinuousOnInterval (fun v => f (c + d * v)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ / |d|, div_pos hδ (abs_pos.mpr hd), ?_⟩
  intro E hE hsmall
  apply hbound (E.1, fun i => (c + d * (E.2 i).1, c + d * (E.2 i).2))
    (affine_disjWithin hE)
  have heq : ∑ i ∈ Finset.range E.1,
      dist (c + d * (E.2 i).1) (c + d * (E.2 i).2) =
      |d| * ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Real.dist_eq]
    rw [show c + d * (E.2 i).1 - (c + d * (E.2 i).2) =
      d * ((E.2 i).1 - (E.2 i).2) by ring, abs_mul]
  rw [heq]
  simpa only [mul_comm] using (lt_div_iff₀ (abs_pos.mpr hd)).mp hsmall

end RothschildStein.G1
