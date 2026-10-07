-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevOperatorData
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Restriction keeps the actual operator jet representatives. -/
def WeakDriftOperatorData.restrict {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) : WeakDriftOperatorData X U p u where
  first := D.first
  square := D.square
  first_weak := fun i => S.hasWeakWordDeriv_restrict X Ω U hU (D.first_weak i)
  square_weak := fun i => S.hasWeakWordDeriv_restrict X Ω U hU (D.square_weak i)
  first_memLp := fun i => (D.first_memLp i).mono_measure (Measure.restrict_mono_set volume hU)
  square_memLp := fun i => (D.square_memLp i).mono_measure (Measure.restrict_mono_set volume hU)

/-- The restricted weak operator is the same function. -/
theorem WeakDriftOperatorData.restrict_operator {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) : (D.restrict U hU).operator = D.operator := rfl

/-- The real operator norm does not increase under domain restriction. -/
theorem WeakDriftOperatorData.restrict_operator_realNorm_le {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) :
    (eLpNorm (D.restrict U hU).operator p (volume.restrict (U : Set (Fin n → ℝ)))).toReal ≤
      (eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal :=
  ENNReal.toReal_mono D.operator_memLp.eLpNorm_ne_top
    (eLpNorm_mono_measure D.operator (Measure.restrict_mono_set volume hU))

end RothschildStein.H3
