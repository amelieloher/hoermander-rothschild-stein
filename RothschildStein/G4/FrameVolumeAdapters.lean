-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VolumePolynomial
public import RothschildStein.G4.CommonWeightBounds
public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The shared integer frame weight is the natural total positive
weight, so the volume polynomial uses ordinary powers (BB pp. 400, 420). -/
theorem frameWeight_eq_nat_sum {ι : Type*} {n : ℕ} (w : ι → ℕ+)
    (B : Fin n → ι) : frameWeight w B = ((∑ i, (w (B i) : ℕ) : ℕ) : ℤ) := by
  simp only [frameWeight, Nat.cast_sum]

/-- Short-frame weights are bounded by dimension times step;
this is the exponent entering the fixed-factor volume bound (BB p. 405). -/
theorem frame_natural_weight_le {ι : Type*} {n s : ℕ} (w : ι → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) (B : Fin n → ι) :
    ∑ i, (w (B i) : ℕ) ≤ n * s := by
  calc
    ∑ i, (w (B i) : ℕ) ≤ ∑ _i : Fin n, s := Finset.sum_le_sum (fun i _ => hw (B i))
    _ = n * s := by simp

end RothschildStein.G4
