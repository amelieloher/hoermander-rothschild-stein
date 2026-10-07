-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteAlgebra
public import RothschildStein.G3.Homogeneity
public import Mathlib.Algebra.Algebra.Equiv
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Diagonal weighted dilation on the fixed coefficient carrier
(BB (10.53)–(10.54), p. 526). -/
def dilate {a : ℕ} (p : Fin a → ℕ+) (t : ℝ) (f : List (Fin a) → ℝ) :
    List (Fin a) → ℝ := fun J => t ^ wordWeight p J * f J

/-- Weighted dilation respects Cauchy multiplication (BB (10.54), p. 526). -/
theorem dilate_convolution {a : ℕ} (p : Fin a → ℕ+) (t : ℝ)
    (f g : List (Fin a) → ℝ) :
    dilate p t (wordConvolution f g) = wordConvolution (dilate p t f) (dilate p t g) := by
  funext J
  simp only [dilate, wordConvolution, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have h := weight_append p (J.take r) (J.drop r)
  rw [List.take_append_drop] at h
  rw [h, pow_add]
  ring

/-- A homogeneous commutator is an eigenvector of dilation
(BB (10.51)–(10.54), pp. 524–526). -/
theorem dilate_formalBracket {a : ℕ} (p : Fin a → ℕ+) (t : ℝ) (I : List (Fin a)) :
    dilate p t (formalBracket I) = t ^ wordWeight p I • formalBracket I := by
  funext J
  by_cases h : wordWeight p J = wordWeight p I
  · simp [dilate, h]
  · simp [dilate, formalBracket_homogeneous p I J h]

/-- Diagonal dilation in the finite carrier (BB p. 526). -/
def finiteDilate {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : WordCoefficients a s p) : WordCoefficients a s p :=
  fun J => t ^ wordWeight p J.val * f J

/-- Finite dilation agrees with restriction of the word dilation (BB p. 526). -/
theorem finiteDilate_restrict {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : List (Fin a) → ℝ) :
    finiteDilate t (restrict f : WordCoefficients a s p) = restrict (dilate p t f) := rfl

/-- Dilation preserves zero extension (BB p. 526). -/
theorem extend_finiteDilate {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : WordCoefficients a s p) : extend (finiteDilate t f) = dilate p t (extend f) := by
  funext J
  by_cases h : wordWeight p J ≤ s <;> simp [extend, finiteDilate, dilate, h, boundedWord]

/-- Dilation is multiplicative in the weighted quotient (BB (10.54), p. 526). -/
theorem finiteDilate_product {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f g : WordCoefficients a s p) :
    finiteDilate t (truncatedProduct f g) =
      truncatedProduct (finiteDilate t f) (finiteDilate t g) := by
  change finiteDilate t (restrict _) = restrict _
  rw [finiteDilate_restrict, extend_finiteDilate, extend_finiteDilate, dilate_convolution]

end RothschildStein.G3
