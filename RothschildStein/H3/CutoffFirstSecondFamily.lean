-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftCutoffBound
public import RothschildStein.H3.SecondCutoffBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Common positive constants for the entire first/second derivative
family. They depend on the fixed fields, gauge and profile, and are independent
of the center, radii, and input function in downstream estimates. -/
theorem exists_cutoff_first_second_constants (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ, 0 < t → t < s → s / 2 ≤ t →
        (∀ i : Fin q, ∀ x : Fin N → ℝ,
          |fieldDerivative (H.fields i.succ) (smoothQuasiballCutoff G ν x₀ t s) x| ≤ c₁ / (s-t)) ∧
        (∀ x : Fin N → ℝ,
          |fieldDerivative (H.fields 0) (smoothQuasiballCutoff G ν x₀ t s) x| ≤ c₂ / (s-t)^2) ∧
        (∀ i j : Fin q, ∀ x : Fin N → ℝ,
          |fieldDerivative (H.fields i.succ)
            (fieldDerivative (H.fields j.succ) (smoothQuasiballCutoff G ν x₀ t s)) x| ≤ c₂ / (s-t)^2) := by
  classical
  let A : Fin q → ℝ := fun i => (exists_horizontal_cutoff_bound G H ν hν i).choose
  let B : Fin q × Fin q → ℝ := fun ij =>
    (exists_secondHorizontal_cutoff_bound G H ν hν ij.1 ij.2).choose
  have hA (i : Fin q) : 0 ≤ A i :=
    (exists_horizontal_cutoff_bound G H ν hν i).choose_spec.1
  have hB (ij : Fin q × Fin q) : 0 ≤ B ij :=
    (exists_secondHorizontal_cutoff_bound G H ν hν ij.1 ij.2).choose_spec.1
  obtain ⟨D, hD, hbD⟩ := exists_drift_cutoff_bound G H ν hν
  let c₁ : ℝ := (∑ i, A i) + 1
  let c₂ : ℝ := D + (∑ ij, B ij) + 1
  have hAs : 0 ≤ ∑ i, A i := Finset.sum_nonneg (fun i _ => hA i)
  have hBs : 0 ≤ ∑ ij, B ij := Finset.sum_nonneg (fun ij _ => hB ij)
  have hAc (i : Fin q) : A i ≤ c₁ := by
    have hs := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
    dsimp [c₁]
    linarith
  have hBc (ij : Fin q × Fin q) : B ij ≤ c₂ := by
    have hs := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ ij)
    dsimp [c₂]
    linarith
  have hDc : D ≤ c₂ := by dsimp [c₂]; linarith
  refine ⟨c₁, c₂, by dsimp [c₁]; linarith, by dsimp [c₂]; linarith, ?_⟩
  intro x₀ t s ht hts hhalf
  have hg : 0 < s-t := sub_pos.mpr hts
  refine ⟨?_, ?_, ?_⟩
  · intro i x
    exact ((exists_horizontal_cutoff_bound G H ν hν i).choose_spec.2 x₀ t s ht hts x).trans
      (div_le_div_of_nonneg_right (hAc i) hg.le)
  · intro x
    exact (hbD x₀ t s ht hts hhalf x).trans
      (div_le_div_of_nonneg_right hDc (sq_nonneg _))
  · intro i j x
    exact ((exists_secondHorizontal_cutoff_bound G H ν hν i j).choose_spec.2 x₀ t s ht hts hhalf x).trans
      (div_le_div_of_nonneg_right (hBc (i,j)) (sq_nonneg _))

end RothschildStein.H3
