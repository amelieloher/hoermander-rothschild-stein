-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.HasWeakHormanderEquation
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Hormander.F

/-- Empty domains have zero restricted measure. When `N = 0`, the carrier
`Fin 0 → ℝ` is a singleton, so every scalar-valued function on it is constant. -/
theorem trivial_cases {N : ℕ} {Ω : Set (Fin N → ℝ)} (_hΩ : IsOpen Ω)
    (u : (Fin N → ℝ) → ℝ) (hcase : Ω = ∅ ∨ N = 0) :
    ∃ f : (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f := by
  rcases hcase with hEmpty | hzero
  · refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    rw [hEmpty]
    change ∀ᵐ x ∂(volume.restrict (∅ : Set (Fin N → ℝ))), u x = 0
    rw [ae_iff]
    simp
  · subst N
    have hconst : u = fun _ : (Fin 0 → ℝ) => u 0 := by
      funext x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
    refine ⟨u, ?_, Filter.EventuallyEq.rfl⟩
    rw [hconst]
    exact contDiffOn_const

/-- The conclusion of Hörmander's theorem in the empty-domain and zero-dimensional cases. -/
theorem edge_cases {k N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (_X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (_c _g : (Fin N → ℝ) → ℝ) (u : (Fin N → ℝ) → ℝ)
    (_hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (_X i) Ω)
    (_hspan : Hormander.Interface.LieAlgebraSpansOn Ω _X)
    (_hc : ContDiffOn ℝ (⊤ : ℕ∞) _c Ω)
    (_hEq : Hormander.Interface.HasWeakHormanderEquation Ω _X _c _g u)
    (hcase : Ω = ∅ ∨ N = 0) :
    ∃ f : (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f :=
  trivial_cases hΩ u hcase

end Hormander.F
