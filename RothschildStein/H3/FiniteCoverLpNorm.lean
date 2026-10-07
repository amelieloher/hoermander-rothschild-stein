-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import RothschildStein.Definitions.memSobolevX
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- an Lp norm on a finitely covered open set is bounded
by the sum of the norms on the covering sets. Overlaps are allowed. -/
theorem eLpNorm_le_finite_open_cover {n : ℕ} {ι : Type*}
    (Ω U : Opens (Fin n → ℝ)) (s : Finset ι) (A : ι → Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (hA : ∀ i ∈ s, (A i : Set (Fin n → ℝ)) ⊆ Ω)
    (hcover : ∀ x ∈ U, ∃ i ∈ s, x ∈ A i)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ)))) :
    eLpNorm f p (volume.restrict (U : Set (Fin n → ℝ))) ≤
      ∑ i ∈ s, eLpNorm f p (volume.restrict (A i : Set (Fin n → ℝ))) := by
  classical
  let μ := volume.restrict (Ω : Set (Fin n → ℝ))
  have hmono : eLpNorm ((U : Set (Fin n → ℝ)).indicator f) p μ ≤
      eLpNorm (∑ i ∈ s, (A i : Set (Fin n → ℝ)).indicator (fun x => ‖f x‖)) p μ := by
    apply eLpNorm_mono_real (hf.indicator U.isOpen.measurableSet).aestronglyMeasurable
    intro x
    simp only [Finset.sum_apply]
    by_cases hx : x ∈ U
    · obtain ⟨i,hi,hxi⟩ := hcover x hx
      rw [Set.indicator_of_mem hx]
      exact (by simpa only [Set.indicator_of_mem hxi] using
        (Finset.single_le_sum (f := fun j => (A j : Set (Fin n → ℝ)).indicator
          (fun y => ‖f y‖) x) (fun j _ => by
            by_cases hj : x ∈ A j <;> simp [hj]) hi))
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact Finset.sum_nonneg (fun j _ => by by_cases hj : x ∈ A j <;> simp [hj])
  have hnormU : eLpNorm ((U : Set (Fin n → ℝ)).indicator f) p μ =
      eLpNorm f p (volume.restrict (U : Set (Fin n → ℝ))) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet]
    dsimp only [μ]
    rw [Measure.restrict_restrict U.isOpen.measurableSet, inter_eq_left.mpr hU]
  rw [← hnormU]
  refine hmono.trans (eLpNorm_sum_le hp |>.trans ?_)
  apply Finset.sum_le_sum
  intro i hi
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (A i).isOpen.measurableSet]
  dsimp only [μ]
  rw [Measure.restrict_restrict (A i).isOpen.measurableSet, inter_eq_left.mpr (hA i hi)]
  exact (eLpNorm_norm f (hf.mono_measure (Measure.restrict_mono_set volume (hA i hi))).aestronglyMeasurable).le

end RothschildStein.H3
