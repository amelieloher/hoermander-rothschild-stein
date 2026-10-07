-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondWeakNorm
public import RothschildStein.H3.WeakHorizontalNorms

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The diagonal square sum is controlled by the complete weighted
second norm, so the interpolation estimate applies to that norm. -/
theorem horizontalSquareWeakENorm_le_driftSecond {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) :
    horizontalSquareWeakENorm X Ω p u ≤ driftSecondWeakENorm X Ω p u := by
  classical
  let f : Fin q → List (Fin (q+1)) := fun i => [i.succ,i.succ]
  have hinj : Function.Injective f := by
    intro i j hij
    have he : i.succ = j.succ := (List.cons.inj hij).1
    exact Fin.succ_injective q he
  have hs : Finset.univ.image f ⊆ driftSecondWordFamily q := by
    intro I hI
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
    rw [mem_driftSecondWordFamily_iff]
    simp [f, wordWeight, driftWeight, Fin.succ_ne_zero]
  have hb := Finset.sum_le_sum_of_subset (f := fun I => weakWordENorm X Ω I p u) hs
  rw [Finset.sum_image (fun i _ j _ hij => hinj hij)] at hb
  exact hb

/-- The full weighted second norm does not increase under domain restriction
for actual Sobolev inputs. -/
theorem driftSecondWeakENorm_mono_domain {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X Ω 2 p u) :
    driftSecondWeakENorm X U p u ≤ driftSecondWeakENorm X Ω p u := by
  apply Finset.sum_le_sum
  intro I hI
  obtain ⟨g, hg, _⟩ := hu.2 I (Finset.mem_filter.mp hI).1
  exact weakWordENorm_mono_domain X Ω U hU I p u g hg

end RothschildStein.H3
