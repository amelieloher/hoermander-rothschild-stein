-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Representatives
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace Hormander.F

/-- Select the local representative at points of the open set and use zero outside it. -/
noncomputable def patchChoice {N : ℕ} {ι : Type*} (Ω : Set (Fin N → ℝ))
    (U : ι → Set (Fin N → ℝ)) (f : ι → (Fin N → ℝ) → ℝ)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i) : (Fin N → ℝ) → ℝ := by
  classical
  exact fun x => if hx : x ∈ Ω then f (Classical.choose (hcover x hx)) x else 0

/-- Choosing a representative on each open patch gives a smooth
function on Ω; the selected value is zero outside Ω. -/
theorem patch_choice_smoothness {N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    {ι : Type*} (U : ι → Set (Fin N → ℝ))
    (f : ι → (Fin N → ℝ) → ℝ) (u : (Fin N → ℝ) → ℝ)
    (hUopen : ∀ i, IsOpen (U i)) (hUsub : ∀ i, U i ⊆ Ω)
    (hcover : ∀ x ∈ Ω, ∃ i, x ∈ U i)
    (hf : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (f i) (U i))
    (hae : ∀ i, f i =ᵐ[volume.restrict (U i)] u) :
    ContDiffOn ℝ (⊤ : ℕ∞) (patchChoice Ω U f hcover) Ω ∧
      ∀ i, EqOn (patchChoice Ω U f hcover) (f i) (U i) := by
  have hcompatible (i j : ι) : EqOn (f i) (f j) (U i ∩ U j) := by
    by_cases hN : 0 < N
    · exact localRepresentatives_agree_on_overlap hN (hUopen i) (hUopen j)
        (hf i).continuousOn (hf j).continuousOn (hae i) (hae j)
    · have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      intro x hx
      exact zeroDimensional_representatives_agree hx (hae i) (hae j)
  constructor
  · intro x hx
    let i : ι := Classical.choose (hcover x hx)
    have hxi : x ∈ U i := Classical.choose_spec (hcover x hx)
    have hpatchEq : patchChoice Ω U f hcover =ᶠ[𝓝 x] f i := by
      filter_upwards [hUopen i |>.mem_nhds hxi] with y hy
      have hyΩ : y ∈ Ω := hUsub i hy
      have hj : y ∈ U (Classical.choose (hcover y hyΩ)) :=
        Classical.choose_spec (hcover y hyΩ)
      simp only [patchChoice, dite_eq_left hyΩ]
      exact (hcompatible i (Classical.choose (hcover y hyΩ)) ⟨hy, hj⟩).symm
    have hfi : ContDiffAt ℝ (⊤ : ℕ∞) (f i) x :=
      (hf i x hxi).contDiffAt ((hUopen i).mem_nhds hxi)
    exact (hfi.congr_of_eventuallyEq hpatchEq).contDiffWithinAt
  · intro i x hx
    have hxΩ : x ∈ Ω := hUsub i hx
    have hj : x ∈ U (Classical.choose (hcover x hxΩ)) :=
      Classical.choose_spec (hcover x hxΩ)
    simp only [patchChoice, dite_eq_left hxΩ]
    exact hcompatible (Classical.choose (hcover x hxΩ)) i ⟨hj, hx⟩

end Hormander.F
