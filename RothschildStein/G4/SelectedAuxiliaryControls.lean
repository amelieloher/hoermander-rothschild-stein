-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedControlAggregation
public import RothschildStein.G4.WeightedBoxes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- A nonzero selected determinant forbids repeated frame fields
(BB Prop 9.52, coefficient aggregation, p. 449). -/
theorem frame_index_injective_of_frameDet_ne_zero {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι) {x : Fin n → ℝ}
    (hdet : frameDet Z B x ≠ 0) : Function.Injective B := by
  intro i j hij
  by_contra hne
  apply hdet
  exact Matrix.det_zero_of_column_eq (M := frameMatrix Z B x) hne
    (fun k => congrArg (fun J => Z J x k) hij)

/-- Combine the selected and auxiliary slots for the same field. -/
def selectedAuxiliaryControls {m n : ℕ} (B : Fin n → Fin m)
    (u : Fin n → ℝ) (v : Fin m → ℝ) (J : Fin m) : ℝ :=
  aggregateMappedControls B u J + v J

/-- Combining the two coefficient families preserves the actual
constant vector field (BB Prop 9.52, p. 449). -/
theorem selectedAuxiliaryControls_field_eq {m n d : ℕ} (B : Fin n → Fin m)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (Z : Fin m → (Fin d → ℝ) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    (∑ J, selectedAuxiliaryControls B u v J • Z J x) =
      ∑ j : Fin (n + m), Fin.append u v j • Z (Fin.addCases B id j) x := by
  simp only [selectedAuxiliaryControls, add_smul, Finset.sum_add_distrib]
  rw [aggregateMappedControls_field_eq, Fin.sum_univ_add]
  simp

/-- Each original field occurs at most once in the selected
frame and once in the auxiliary family. Strict coefficient bounds
therefore give cost less than 2ar, with no dimension factor
(BB Prop 9.52, final box inclusion, p. 449). -/
theorem selectedAuxiliaryControls_mem_doubleBox {m n : ℕ}
    (w : Fin m → ℕ+) (B : Fin n → Fin m) (hB : Function.Injective B)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) (hr : 0 < r)
    {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : u ∈ weightedBox (w ∘ B) (a * r)) (hv : v ∈ weightedBox w (b * r)) :
    selectedAuxiliaryControls B u v ∈ weightedBox w (2 * a * r) := by
  classical
  intro J
  have hselected : |aggregateMappedControls B u J| ≤ (a * r) ^ (w J : ℕ) := by
    by_cases hJ : ∃ i, B i = J
    · obtain ⟨i, rfl⟩ := hJ
      have heq : aggregateMappedControls B u (B i) = u i := by
        simp [aggregateMappedControls, hB.eq_iff]
      rw [heq]
      exact (hu i).le
    · have heq : aggregateMappedControls B u J = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact ite_eq_right (fun hi => hJ ⟨i, hi⟩)
      rw [heq, abs_zero]
      positivity
  calc
    |selectedAuxiliaryControls B u v J| ≤ |aggregateMappedControls B u J| + |v J| := abs_add_le _ _
    _ < (a * r) ^ (w J : ℕ) + (b * r) ^ (w J : ℕ) :=
      add_lt_add_of_le_of_lt hselected (hv J)
    _ ≤ (a * r + b * r) ^ (w J : ℕ) :=
      pow_add_pow_le (mul_nonneg ha.le hr.le) (mul_nonneg hb.le hr.le) (w J).ne_zero
    _ ≤ (2 * a * r) ^ (w J : ℕ) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _

/-- The chart shift alone has exactly the auxiliary controls
(BB Prop 9.52, (9.49), p. 449). -/
theorem selectedAuxiliaryControls_zero {m n : ℕ} (B : Fin n → Fin m) (v : Fin m → ℝ) :
    selectedAuxiliaryControls B 0 v = v := by
  ext J
  simp [selectedAuxiliaryControls, aggregateMappedControls]

end RothschildStein.G4
