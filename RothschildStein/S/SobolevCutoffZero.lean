-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactSobolevZero
public import RothschildStein.S.SobolevMultiplication

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Multiplication by an interior smooth compact test sends
Sobolev data to the exact zero-boundary class (BB Cor 2.10,
p. 73). The approximants are ordinary compact mollifications. -/
theorem memSobolevXZero_mul_test (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (hpt : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    memSobolevXZero w X Ω k p (fun x => f x * φ x) :=
  memSobolevXZero_of_compact_support w X Ω hX k hpt
    (memSobolevX_mul_test w X Ω hX k p Fact.out f hf φ)
    (φ.hasCompactSupport.mul_left)
    (tsupport_mul_subset_right.trans φ.tsupport_subset)

end RothschildStein.S
