-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedPartialLiftExtension
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Compatible partial lifts glue up to the supremum of their
lifetimes, preserving the actual lift identity and each weighted speed
bound. Compatibility is supplied by local chart uniqueness, and no
endpoint limit is assumed (BB Prop 9.52, p. 449). -/
theorem exists_coherent_partialLift_to_supremum {n : ℕ}
    (w : Fin n → ℕ+) (S : Set ℝ) (hS : S.Nonempty)
    (θ : S → ℝ → (Fin n → ℝ))
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    (U : Set (Fin n → ℝ)) {r C b : ℝ}
    (hzero : ∀ T, θ T 0 = 0)
    (hcompat : ∀ T₁ T₂ : S, ∀ t ∈ Icc (0 : ℝ) (min (T₁ : ℝ) T₂), θ T₁ t = θ T₂ t)
    (hlift : ∀ T : S, ∀ t ∈ Icc (0 : ℝ) T, F (θ T t) = γ t)
    (hrange : ∀ T : S, ∀ t ∈ Icc (0 : ℝ) T, θ T t ∈ U)
    (hvariation : ∀ T : S, ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
      |θ T τ i - θ T σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ|) :
    ∃ Θ : ℝ → (Fin n → ℝ), Θ 0 = 0 ∧
      (∀ t ∈ Ico (0 : ℝ) (sSup S), F (Θ t) = γ t) ∧
      (∀ t ∈ Ico (0 : ℝ) (sSup S), Θ t ∈ U) ∧
      ∀ σ ∈ Ico (0 : ℝ) (sSup S), ∀ τ ∈ Ico (0 : ℝ) (sSup S), ∀ i,
        |Θ τ i - Θ σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ| := by
  classical
  let Θ : ℝ → (Fin n → ℝ) := fun t =>
    if ht : t ∈ Ico (0 : ℝ) (sSup S) then
      θ ⟨(exists_lt_of_lt_csSup hS ht.2).choose,
        (exists_lt_of_lt_csSup hS ht.2).choose_spec.1⟩ t
    else 0
  have heq (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (sSup S)) (T : S) (htT : t ≤ T) :
      Θ t = θ T t := by
    dsimp only [Θ]
    rw [dite_eq_left ht]
    apply hcompat
    exact ⟨ht.1, le_min (exists_lt_of_lt_csSup hS ht.2).choose_spec.2.le htT⟩
  refine ⟨Θ, ?_, ?_, ?_, ?_⟩
  · by_cases h0 : (0 : ℝ) ∈ Ico (0 : ℝ) (sSup S)
    · dsimp only [Θ]
      rw [dite_eq_left h0]
      exact hzero _
    · simp only [Θ, dite_eq_right h0]
  · intro t ht
    obtain ⟨T, hTS, htT⟩ := exists_lt_of_lt_csSup hS ht.2
    rw [heq t ht ⟨T, hTS⟩ htT.le]
    exact hlift ⟨T, hTS⟩ t ⟨ht.1, htT.le⟩
  · intro t ht
    obtain ⟨T, hTS, htT⟩ := exists_lt_of_lt_csSup hS ht.2
    rw [heq t ht ⟨T, hTS⟩ htT.le]
    exact hrange ⟨T, hTS⟩ t ⟨ht.1, htT.le⟩
  · intro σ hσ τ hτ i
    obtain ⟨T, hTS, hmaxT⟩ := exists_lt_of_lt_csSup hS (max_lt hσ.2 hτ.2)
    have hσT : σ ≤ T := (le_max_left σ τ).trans hmaxT.le
    have hτT : τ ≤ T := (le_max_right σ τ).trans hmaxT.le
    rw [heq σ hσ ⟨T, hTS⟩ hσT, heq τ hτ ⟨T, hTS⟩ hτT]
    exact hvariation ⟨T, hTS⟩ σ ⟨hσ.1, hσT⟩ τ ⟨hτ.1, hτT⟩ i

end RothschildStein.G4
