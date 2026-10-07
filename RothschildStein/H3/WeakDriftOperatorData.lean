-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasWeakWordDeriv
public import RothschildStein.Definitions.memSobolevX

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal

/-- Weak jet representatives of the fixed drift operator on a Sobolev input. -/
structure WeakDriftOperatorData {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) where
  first : Fin (q+1) → (Fin n → ℝ) → ℝ
  square : Fin q → (Fin n → ℝ) → ℝ
  first_weak : ∀ i, hasWeakWordDeriv X Ω [i] u (first i)
  first_memLp : ∀ i, MemLp (first i) p (volume.restrict (Ω : Set (Fin n → ℝ)))
  square_weak : ∀ i, hasWeakWordDeriv X Ω [i.succ,i.succ] u (square i)
  square_memLp : ∀ i, MemLp (square i) p (volume.restrict (Ω : Set (Fin n → ℝ)))

/-- The weak operator represented by these drift and square jets. -/
def WeakDriftOperatorData.operator {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) : (Fin n → ℝ) → ℝ :=
  fun x => D.first 0 x+∑ i, D.square i x

end RothschildStein.H3
