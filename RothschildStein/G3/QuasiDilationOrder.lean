-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiExponentialJet
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted dilation preserves every filtration order,
including the zero parameter (BB pp. 417–420). -/
theorem finiteDilate_weight_order {a s k : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast k (coefficientDilationHom t f) := by
  rw [finiteOrderAtLeast_iff] at hf ⊢
  intro J hJ
  change t ^ wordWeight p J.val * f J = 0
  rw [hf J hJ, mul_zero]

/-- The scaled quasi-exponential retains its positive leading
word at every real parameter, with the full next-weight error. -/
theorem quasiExponentialLogAt_leading_order {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (t : ℝ) (I : List (Fin a)) :
    FiniteOrderAtLeast (wordWeight p I + 1)
      ((quasiExponentialLogAt (s := s) (p := p) t I).val -
        t ^ wordWeight p I • finiteBracketWord I) := by
  have hh := finiteDilate_weight_order t (quasiExponentialLog_leading (p := p) hs I).2
  rw [map_sub] at hh
  have hb : coefficientDilationHom (a := a) (s := s) (p := p) t (finiteBracketWord I) =
      t ^ wordWeight p I • finiteBracketWord I := by
    change finiteDilate t (truncatedBracket I) = t ^ wordWeight p I • truncatedBracket I
    exact finiteDilate_truncatedBracket t I
  rw [hb] at hh
  exact hh
end RothschildStein.G3
