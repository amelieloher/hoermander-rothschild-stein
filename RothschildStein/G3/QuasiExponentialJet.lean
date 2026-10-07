-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiExponentialLeadingWord
public import RothschildStein.G3.WeightedLieComponents
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The fixed homogeneous correction coefficients in the signed
quasi-exponential logarithm (BB (9.13), p. 417). -/
def quasiJetComponent {a s : ℕ} {p : Fin a → ℕ+} (I : List (Fin a)) (k : ℕ) :
    WordCoefficients a s p :=
  let f : WordCoefficients a s p := (quasiExponentialLog (s := s) (p := p) I).val
  weightProjection k (f - truncatedBracket I)

/-- Every correction coefficient of weight at most the leading word
weight is zero (BB Lemma 9.26, pp. 417–419). -/
theorem quasiJetComponent_eq_zero {a s : ℕ} {p : Fin a → ℕ+} (hs : 1 ≤ s)
    (I : List (Fin a)) {k : ℕ} (hk : k ≤ wordWeight p I) :
    quasiJetComponent (s := s) (p := p) I k = 0 :=
  weightProjection_eq_zero_of_order (quasiExponentialLog_leading hs I).2 (by omega)

/-- Exact finite weighted logarithmic jet, with a positive leading
word and constant homogeneous corrections (BB (9.13), p. 417). -/
theorem quasiExponentialLogAt_jet {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (I : List (Fin a)) :
    let g : WordCoefficients a s p := (quasiExponentialLogAt (s := s) (p := p) t I).val
    g =
      t ^ wordWeight p I • (truncatedBracket I : WordCoefficients a s p) +
        ∑ k ∈ Finset.range (s + 1), t ^ k • quasiJetComponent I k := by
  let f : WordCoefficients a s p := (quasiExponentialLog (s := s) (p := p) I).val
  have he : f = truncatedBracket I + (f - truncatedBracket I) := by abel
  change finiteDilate t f = _
  conv_lhs => rw [he]
  change dilationLinearMap t _ = _
  rw [map_add]
  change finiteDilate t (truncatedBracket I) + finiteDilate t (f - truncatedBracket I) = _
  rw [finiteDilate_truncatedBracket, finiteDilate_eq_sum_projections]
  simp only [f, quasiJetComponent]
end RothschildStein.G3
