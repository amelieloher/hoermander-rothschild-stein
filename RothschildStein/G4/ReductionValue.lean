-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GlobalReduction
public import RothschildStein.G4.FiniteJetBounds
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Universal field-value space, independent of the actual fields. -/
abbrev ReductionValues (p n : ℕ) := (Fin p ⊕ Unit) → (Fin n → ℝ)

/-- Universal determinant polynomial on field values. -/
def valueFrameDet {p n : ℕ} (B : Fin n → Fin p) (u : ReductionValues p n) : ℝ :=
  Matrix.det (Matrix.of (fun k j => u (Sum.inl (B j)) k))

/-- Universal replacement determinant polynomial. -/
def valueReplacementDet {p n : ℕ} (B : Fin n → Fin p) (i : Fin n)
    (u : ReductionValues p n) : ℝ :=
  Matrix.det (Matrix.updateCol (Matrix.of (fun k j => u (Sum.inl (B j)) k)) i
    (u (Sum.inr ())))

/-- Universal sum-of-squares denominator. -/
def valueDenominator {p n : ℕ} (u : ReductionValues p n) : ℝ :=
  ∑ B : Fin n → Fin p, valueFrameDet B u ^ 2

/-- Universal rational coefficient, specialized by field values. -/
def valueReduction {p n : ℕ} (J : Fin p) (u : ReductionValues p n) : ℝ :=
  (∑ B : Fin n → Fin p, ∑ i : Fin n,
    if B i = J then valueFrameDet B u * valueReplacementDet B i u else 0) /
      valueDenominator u

/-- The determinant polynomial is smooth on the whole value space. -/
theorem valueFrameDet_contDiff {p n : ℕ} (B : Fin n → Fin p) :
    ContDiff ℝ (⊤ : ℕ∞) (valueFrameDet B) := by
  classical
  unfold valueFrameDet
  simp only [Matrix.det_apply', Matrix.of_apply]
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro j hj
  exact contDiff_apply_apply ℝ ℝ (Sum.inl (B j)) (σ j)

/-- Replacement determinants are smooth on the whole value space. -/
theorem valueReplacementDet_contDiff {p n : ℕ} (B : Fin n → Fin p) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (valueReplacementDet B i) := by
  classical
  unfold valueReplacementDet
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [Matrix.updateCol_apply]
    exact contDiff_apply_apply ℝ ℝ (Sum.inr () : Fin p ⊕ Unit) (σ i)
  · simp only [Matrix.updateCol_apply, ite_eq_right hji, Matrix.of_apply]
    exact contDiff_apply_apply ℝ ℝ (Sum.inl (B j)) (σ j)

/-- The denominator is a globally smooth universal polynomial. -/
theorem valueDenominator_contDiff {p n : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (@valueDenominator p n) :=
  ContDiff.sum (fun B _ => (valueFrameDet_contDiff B).pow 2)

/-- Universal rational coefficients are smooth on their open domain. -/
theorem valueReduction_contDiffOn {p n : ℕ} (J : Fin p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (valueReduction (n := n) J) {u | valueDenominator u ≠ 0} := by
  apply ContDiffOn.div _ valueDenominator_contDiff.contDiffOn (fun u hu => hu)
  apply ContDiffOn.sum
  intro B hB
  apply ContDiffOn.sum
  intro i hi
  split_ifs
  · exact ((valueFrameDet_contDiff B).mul (valueReplacementDet_contDiff B i)).contDiffOn
  · exact contDiffOn_const

/-- The nonzero denominator domain is open. -/
theorem valueDenominator_domain_isOpen {p n : ℕ} :
    IsOpen {u : ReductionValues p n | valueDenominator u ≠ 0} :=
  isOpen_ne_fun valueDenominator_contDiff.continuous continuous_const

/-- The universal bounded nondegenerate value set is compact. -/
theorem valueSet_isCompact {p n : ℕ} (H Δ : ℝ) :
    IsCompact (Metric.closedBall (0 : ReductionValues p n) H ∩
      {u | Δ ^ 2 ≤ valueDenominator u}) := by
  exact (isCompact_closedBall 0 H).inter_right
    (isClosed_le continuous_const valueDenominator_contDiff.continuous)

end RothschildStein.G4
