-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.BasisVec
public import Hormander.Interface.LieWord
public import Hormander.Interface.LieWordEval
public import Hormander.Interface.LieAlgebraSpansOn
public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.HormanderAdjointTest
public import Hormander.Interface.HasWeakHormanderEquation
public import Hormander.Provider.Facade

/-!
# Hörmander's hypoellipticity theorem

Re-exports the definitions of the weak Hörmander equation and the bracket condition, and states
Hörmander's theorem `Hormander.Interface.exists_smooth_aeRepresentative`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- Hörmander's hypoellipticity theorem (1967, Theorem 1.1) for `X₀ + Σ Xᵢ² + c`:
a locally integrable weak solution agrees almost everywhere with a smooth function. -/
theorem exists_smooth_aeRepresentative
    {k N : ℕ} {Ω : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω)
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hspan : LieAlgebraSpansOn Ω X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (hEq : HasWeakHormanderEquation Ω X c g u) :
    ∃ f : (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f :=
  by exact Hormander.Provider.exists_smooth_aeRepresentative hΩ X c g u hX hspan hc hEq

end Hormander.Interface
