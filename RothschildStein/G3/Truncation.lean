-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Convolution
public import RothschildStein.G3.FiniteWords
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Restriction to the fixed finite coefficient carrier (BB p. 525). -/
def restrict {a s : ℕ} {p : Fin a → ℕ+} (f : List (Fin a) → ℝ) :
    WordCoefficients a s p := fun J => f (boundedWordList J)

/-- Zero extension of a bounded coefficient family (BB pp. 524–525). -/
def extend {a s : ℕ} {p : Fin a → ℕ+} (f : WordCoefficients a s p) :
    List (Fin a) → ℝ := fun J =>
  if h : wordWeight p J ≤ s then f (boundedWord p J h) else 0

/-- Restriction recovers the finite coefficient family (BB p. 525). -/
@[simp] theorem restrict_extend {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) : restrict (extend f) = f := by
  funext J
  simp only [restrict, extend, dite_eq_left (boundedWord_weight J)]
  rfl

/-- Zero extension preserves all coefficients through the cutoff (BB p. 525). -/
theorem extend_restrict {a s : ℕ} {p : Fin a → ℕ+}
    (f : List (Fin a) → ℝ) (J : List (Fin a)) (h : wordWeight p J ≤ s) :
    extend (restrict f : WordCoefficients a s p) J = f J := by
  simp [extend, h, restrict, boundedWord_list]

/-- Zero extension is additive (BB p. 525). -/
@[simp] theorem extend_add {a s : ℕ} {p : Fin a → ℕ+}
    (f g : WordCoefficients a s p) : extend (f + g) = extend f + extend g := by
  funext J
  by_cases h : wordWeight p J ≤ s <;> simp [extend, h]

/-- Zero extension respects scalar multiplication (BB p. 525). -/
@[simp] theorem extend_smul {a s : ℕ} {p : Fin a → ℕ+}
    (r : ℝ) (f : WordCoefficients a s p) : extend (r • f) = r • extend f := by
  funext J
  by_cases h : wordWeight p J ≤ s <;> simp [extend, h]

/-- Zero extension preserves zero (BB p. 525). -/
@[simp] theorem extend_zero {a s : ℕ} {p : Fin a → ℕ+} :
    extend (0 : WordCoefficients a s p) = 0 := by
  funext J
  simp [extend]

/-- Multiplication depends only on coefficients through the cutoff
(BB Proposition 10.44, p. 525). -/
theorem convolution_eq_of_eq_through {a s : ℕ} {p : Fin a → ℕ+}
    {f f' g g' : List (Fin a) → ℝ}
    (hf : ∀ J, wordWeight p J ≤ s → f J = f' J)
    (hg : ∀ J, wordWeight p J ≤ s → g J = g' J)
    (J : List (Fin a)) (hJ : wordWeight p J ≤ s) :
    wordConvolution f g J = wordConvolution f' g' J := by
  unfold wordConvolution
  apply Finset.sum_congr rfl
  intro r _
  rw [hf _ ((weight_take_le p J r).trans hJ),
    hg _ ((weight_drop_le p J r).trans hJ)]

/-- Associative multiplication on the fixed truncated carrier
(BB Proposition 10.44, pp. 524–525). -/
def truncatedProduct {a s : ℕ} {p : Fin a → ℕ+}
    (f g : WordCoefficients a s p) : WordCoefficients a s p :=
  restrict (wordConvolution (extend f) (extend g))

/-- Truncation is compatible with associative multiplication (BB p. 525). -/
theorem restrict_convolution {a s : ℕ} {p : Fin a → ℕ+}
    (f g : List (Fin a) → ℝ) :
    truncatedProduct (restrict f : WordCoefficients a s p) (restrict g) =
      restrict (wordConvolution f g) := by
  funext J
  exact convolution_eq_of_eq_through (extend_restrict f) (extend_restrict g)
    (boundedWordList J) (boundedWord_weight J)

/-- Truncated multiplication is additive in the right input (BB p. 525). -/
theorem truncatedProduct_add_right {a s : ℕ} {p : Fin a → ℕ+}
    (f g h : WordCoefficients a s p) :
    truncatedProduct f (g + h) = truncatedProduct f g + truncatedProduct f h := by
  funext J
  change wordConvolution (extend f) (extend (g + h)) _ = _
  rw [extend_add, convolution_add_right]
  rfl

/-- Truncated multiplication is additive in the left input (BB p. 525). -/
theorem truncatedProduct_add_left {a s : ℕ} {p : Fin a → ℕ+}
    (f g h : WordCoefficients a s p) :
    truncatedProduct (f + g) h = truncatedProduct f h + truncatedProduct g h := by
  funext J
  change wordConvolution (extend (f + g)) (extend h) _ = _
  rw [extend_add, convolution_add_left]
  rfl

/-- Scalar multiplication commutes with the left input (BB p. 525). -/
theorem truncatedProduct_smul_left {a s : ℕ} {p : Fin a → ℕ+}
    (r : ℝ) (f g : WordCoefficients a s p) :
    truncatedProduct (r • f) g = r • truncatedProduct f g := by
  funext J
  change wordConvolution (extend (r • f)) (extend g) _ = _
  rw [extend_smul, convolution_smul_left]
  rfl

/-- Scalar multiplication commutes with the right input (BB p. 525). -/
theorem truncatedProduct_smul_right {a s : ℕ} {p : Fin a → ℕ+}
    (r : ℝ) (f g : WordCoefficients a s p) :
    truncatedProduct f (r • g) = r • truncatedProduct f g := by
  funext J
  change wordConvolution (extend f) (extend (r • g)) _ = _
  rw [extend_smul, convolution_smul_right]
  rfl

/-- The finite weighted quotient has associative multiplication (BB p. 525). -/
theorem truncatedProduct_assoc {a s : ℕ} {p : Fin a → ℕ+}
    (f g h : WordCoefficients a s p) :
    truncatedProduct (truncatedProduct f g) h =
      truncatedProduct f (truncatedProduct g h) := by
  rw [← restrict_extend h, ← restrict_extend f, ← restrict_extend g]
  rw [restrict_convolution, restrict_convolution, restrict_convolution,
    restrict_convolution]
  funext J
  exact convolution_assoc _ _ _ _

/-- The empty word supplies the unit in the weighted quotient (BB p. 525). -/
def truncatedUnit {a s : ℕ} {p : Fin a → ℕ+} : WordCoefficients a s p :=
  restrict wordUnit

/-- Left unit in the weighted quotient (BB p. 525). -/
theorem truncatedProduct_unit_left {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) : truncatedProduct truncatedUnit f = f := by
  rw [← restrict_extend f]
  change truncatedProduct (restrict wordUnit) (restrict (extend f)) = _
  rw [restrict_convolution]
  funext J
  exact convolution_unit_left _ _

/-- Right unit in the weighted quotient (BB p. 525). -/
theorem truncatedProduct_unit_right {a s : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) : truncatedProduct f truncatedUnit = f := by
  rw [← restrict_extend f]
  change truncatedProduct (restrict (extend f)) (restrict wordUnit) = _
  rw [restrict_convolution]
  funext J
  exact convolution_unit_right _ _

end RothschildStein.G3
