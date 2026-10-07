-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiDilationOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A signed homogeneous layer correction. The root is a choice
of a constant real parameter; no smooth dependence on its coefficient is
asserted at zero (BB Theorem 9.25, pp. 419–420). -/
def signedQuasiCorrection {a s : ℕ} {p : Fin a → ℕ+}
    (b : ℝ) (I : List (Fin a)) : coefficientLieAlgebra a s p :=
  let t := |b| ^ ((wordWeight p I : ℝ)⁻¹)
  if 0 ≤ b then quasiExponentialLogAt t I else -quasiExponentialLogAt t I

/-- The nonnegative root has the exact requested leading coefficient
for every nonempty word (BB Theorem 9.25, pp. 419–420). -/
theorem quasiCorrection_root_pow {a : ℕ} (p : Fin a → ℕ+)
    (b : ℝ) (I : List (Fin a)) (hne : I ≠ []) :
    (|b| ^ ((wordWeight p I : ℝ)⁻¹)) ^ wordWeight p I = |b| := by
  apply Real.rpow_inv_natCast_pow (abs_nonneg b)
  have hl : 0 < I.length := List.length_pos_iff.mpr hne
  have hw := length_le_weight p I
  omega

/-- Signed root corrections produce b times the chosen bracket,
with no lower layer and a next-weight remainder (BB pp. 419–420). -/
theorem signedQuasiCorrection_leading_order {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (b : ℝ) (I : List (Fin a)) (hne : I ≠ []) :
    FiniteOrderAtLeast (wordWeight p I + 1)
      ((signedQuasiCorrection (s := s) (p := p) b I).val -
        b • (finiteBracketWord I : FiniteWordAlgebra a s p)) := by
  let t : ℝ := |b| ^ ((wordWeight p I : ℝ)⁻¹)
  have ht : t ^ wordWeight p I = |b| := quasiCorrection_root_pow p b I hne
  have hh := quasiExponentialLogAt_leading_order (p := p) hs t I
  rw [ht] at hh
  by_cases hb : 0 ≤ b
  · rw [signedQuasiCorrection, ite_eq_left hb]
    simpa only [t, abs_of_nonneg hb] using hh
  · rw [signedQuasiCorrection, ite_eq_right hb]
    have hab : |b| = -b := abs_of_neg (lt_of_not_ge hb)
    rw [hab] at hh
    have hn := finiteOrderAtLeast_smul hh (-1 : ℝ)
    have he : (-1 : ℝ) • ((quasiExponentialLogAt (s := s) (p := p) t I).val -
        (-b) • (finiteBracketWord I : FiniteWordAlgebra a s p)) =
        -(quasiExponentialLogAt t I).val - b • finiteBracketWord I := by
      simp only [smul_sub, neg_smul, one_smul, neg_neg]
    rw [he] at hn
    exact hn
end RothschildStein.G3
