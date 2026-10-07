-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CoordinatePartialWords
public import RothschildStein.G3.FiniteSmoothSymmetry
public import Mathlib.Data.Fin.Tuple.Sort
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Standard coordinate multiindices are represented by sorted direction lists.
The bound covers every component and every total order through R. -/
def CoordinateMultiIndexBudget {a N : ℕ} (Ω : Set (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) (R : ℕ) (B : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ i k, k ≤ R → ∀ dirs : Fin k → Fin N, Monotone dirs → ∀ j : Fin N,
    |coordinatePartialWord (List.ofFn dirs) (X i) x j| ≤ B

/-- Finite Schwarz symmetry converts canonical coordinate partials to all jets. -/
theorem coordinateFieldJetBudget_of_multiIndex_budget {a N R : ℕ}
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {B : ℝ}
    (h : CoordinateMultiIndexBudget Ω X R B) : CoordinateFieldJetBudget Ω X R B := by
  intro x hx i k hk dirs j
  have he := h x hx i k hk (dirs ∘ Tuple.sort dirs) (Tuple.monotone_sort dirs) j
  rw [coordinatePartialWord_ofFn_eq_iteratedFDeriv hΩ (hX i) _ hx] at he
  have hp := iteratedFDeriv_perm_of_finite_smoothness
    (((hX i).contDiffAt (hΩ.mem_nhds hx)).of_le (by simp : (k : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))
    (Tuple.sort dirs) (fun l => Pi.single (dirs l) (1 : ℝ))
  have hp' : iteratedFDeriv ℝ k (X i) x
      (fun l => Pi.single ((dirs ∘ Tuple.sort dirs) l) (1 : ℝ)) =
      iteratedFDeriv ℝ k (X i) x (fun l => Pi.single (dirs l) (1 : ℝ)) := hp
  rw [hp'] at he
  exact he

/-- The source's coordinate coefficient seminorm controls ambient Frechet jets. -/
theorem norm_field_jets_le_of_multiIndex_budget {a N R : ℕ}
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) {B : ℝ} (hB : 0 ≤ B)
    (h : CoordinateMultiIndexBudget Ω X R B) :
    ∀ x ∈ Ω, ∀ i k, k ≤ R →
      ‖iteratedFDeriv ℝ k (X i) x‖ ≤ (max 1 (N : ℝ))^R*B :=
  norm_field_jets_le_of_coordinate_budget Ω X hB
    (coordinateFieldJetBudget_of_multiIndex_budget hΩ X hX h)
end RothschildStein.G3
