-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ChangeCutoff
public import RothschildStein.G3.LieWords
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Ordinary-degree truncation of the completed word algebra (BB p. 467). -/
def ordinaryTrunc {a : ℕ} (s : ℕ) (f : CoefficientSeries a) :
    FiniteWordAlgebra a s (fun _ => 1) := truncateSeries f

/-- Positive degree in the completion means zero constant coefficient
(BB pp. 467–468). -/
def PositiveSeries {a : ℕ} (f : CoefficientSeries a) : Prop := coefficient f [] = 0

/-- Every finite truncation of a positive-degree series has positive order
(BB pp. 467–468). -/
theorem ordinaryTrunc_positive {a : ℕ} {f : CoefficientSeries a}
    (hf : PositiveSeries f) (s : ℕ) : FiniteOrderAtLeast 1 (ordinaryTrunc s f) := by
  apply (finite_positive_order_iff _).mpr
  exact hf

/-- Ordinary word weight equals ordinary letter count (BB p. 467). -/
theorem ordinary_weight {a : ℕ} (J : List (Fin a)) :
    wordWeight (fun _ : Fin a => 1) J = J.length := by
  simp [wordWeight]

/-- Ordinary truncations are consistent (BB (9.75), p. 468). -/
theorem cutoffHom_ordinaryTrunc {a s t : ℕ} (hst : s ≤ t) (f : CoefficientSeries a) :
    cutoffHom hst (ordinaryTrunc t f) = ordinaryTrunc s f := rfl

/-- Degreewise formal exponential on positive-degree inputs in the noncommutative
completion (BB pp. 467–469). Only finitely many powers contribute to each word. -/
def formalExp {a : ℕ} (f : CoefficientSeries a) : CoefficientSeries a := fun J =>
  finiteExp (ordinaryTrunc J.length f)
    (boundedWord (fun _ => 1) J (by rw [ordinary_weight]))

/-- The completed exponential agrees with every finite-degree exponential
(BB pp. 467–469). -/
theorem ordinaryTrunc_formalExp {a : ℕ} {f : CoefficientSeries a}
    (hf : PositiveSeries f) (s : ℕ) :
    ordinaryTrunc s (formalExp f) = finiteExp (ordinaryTrunc s f) := by
  funext J
  have hlen : J.val.length ≤ s := by
    simpa only [ordinary_weight, boundedWordList] using boundedWord_weight J
  have h := cutoffHom_finiteExp hlen (ordinaryTrunc_positive hf s)
  rw [cutoffHom_ordinaryTrunc] at h
  have he := congrFun h (boundedWord (fun _ => 1) J.val (by rw [ordinary_weight]))
  exact he.symm

/-- Formal exponentiation is injective on all positive-degree series,
without a convergence assertion (BB Proposition 9.72, pp. 475–476). -/
theorem formalExp_injective_positive {a : ℕ} {f g : CoefficientSeries a}
    (hf : PositiveSeries f) (hg : PositiveSeries g) (he : formalExp f = formalExp g) : f = g := by
  funext J
  have hs : finiteExp (ordinaryTrunc J.length f) = finiteExp (ordinaryTrunc J.length g) := by
    rw [← ordinaryTrunc_formalExp hf, ← ordinaryTrunc_formalExp hg, he]
  have ht := finiteExp_injective_positive (ordinaryTrunc_positive hf J.length)
    (ordinaryTrunc_positive hg J.length) hs
  exact congrFun ht (boundedWord (fun _ => 1) J (by rw [ordinary_weight]))

end RothschildStein.G3
