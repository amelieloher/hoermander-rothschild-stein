-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CompletedExponential
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Degreewise BCH on positive-degree inputs in the associative noncommutative completion
(BB Theorem 9.68, pp. 469–471). Its Lie-polynomial coefficients are separate. -/
def formalBCH {a : ℕ} (f g : CoefficientSeries a) : CoefficientSeries a := fun J =>
  finiteBCH (ordinaryTrunc J.length f) (ordinaryTrunc J.length g)
    (boundedWord (fun _ => 1) J (by rw [ordinary_weight]))

/-- The completed BCH logarithm has positive degree (BB p. 470). -/
theorem formalBCH_positive {a : ℕ} {f g : CoefficientSeries a}
    (hf : PositiveSeries f) (hg : PositiveSeries g) : PositiveSeries (formalBCH f g) := by
  exact (finite_positive_order_iff _).mp
    (finiteBCH_order (ordinaryTrunc_positive hf 0) (ordinaryTrunc_positive hg 0))

/-- Formal BCH agrees with every finite-degree quotient (BB pp. 468–470). -/
theorem ordinaryTrunc_formalBCH {a : ℕ} {f g : CoefficientSeries a}
    (hf : PositiveSeries f) (hg : PositiveSeries g) (s : ℕ) :
    ordinaryTrunc s (formalBCH f g) = finiteBCH (ordinaryTrunc s f) (ordinaryTrunc s g) := by
  funext J
  have hlen : J.val.length ≤ s := by
    simpa only [ordinary_weight, boundedWordList] using boundedWord_weight J
  have h := cutoffHom_finiteBCH hlen (ordinaryTrunc_positive hf s) (ordinaryTrunc_positive hg s)
  rw [cutoffHom_ordinaryTrunc, cutoffHom_ordinaryTrunc] at h
  exact (congrFun h (boundedWord (fun _ => 1) J.val (by rw [ordinary_weight]))).symm

/-- Ordinary truncation respects the associative product (BB p. 468). -/
theorem ordinaryTrunc_mul {a : ℕ} (s : ℕ) (f g : CoefficientSeries a) :
    ordinaryTrunc s (f * g) = ordinaryTrunc s f * ordinaryTrunc s g :=
  (truncateSeries (a := a) (s := s) (p := fun _ => 1)).map_mul f g

/-- Formal BCH satisfies its defining exponential identity coefficientwise
(BB (9.76), p. 470). -/
theorem formalExp_BCH {a : ℕ} {f g : CoefficientSeries a}
    (hf : PositiveSeries f) (hg : PositiveSeries g) :
    formalExp (formalBCH f g) = formalExp f * formalExp g := by
  funext J
  have h : ordinaryTrunc J.length (formalExp (formalBCH f g)) =
      ordinaryTrunc J.length (formalExp f * formalExp g) := by
    rw [ordinaryTrunc_formalExp (formalBCH_positive hf hg), ordinaryTrunc_formalBCH hf hg,
      ordinaryTrunc_mul, ordinaryTrunc_formalExp hf, ordinaryTrunc_formalExp hg,
      finiteExp_BCH (ordinaryTrunc_positive hf J.length) (ordinaryTrunc_positive hg J.length)]
  exact congrFun h (boundedWord (fun _ => 1) J (by rw [ordinary_weight]))

/-- Uniqueness of the positive-degree associative formal BCH logarithm
(BB Theorem 9.68, pp. 469–471). -/
theorem formalBCH_unique {a : ℕ} {f g h : CoefficientSeries a}
    (hf : PositiveSeries f) (hg : PositiveSeries g) (hh : PositiveSeries h)
    (he : formalExp h = formalExp f * formalExp g) : h = formalBCH f g :=
  formalExp_injective_positive hh (formalBCH_positive hf hg) (he.trans (formalExp_BCH hf hg).symm)

end RothschildStein.G3
