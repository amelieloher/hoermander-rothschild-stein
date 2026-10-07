-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Dilation
public import RothschildStein.G3.LieSpan
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted dilation is a real linear map on the fixed carrier (BB p. 526). -/
def dilationLinearMap {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ) :
    WordCoefficients a s p →ₗ[ℝ] WordCoefficients a s p where
  toFun := finiteDilate t
  map_add' f g := by
    funext J
    change _ * (f J + g J) = _ * f J + _ * g J
    ring
  map_smul' r f := by
    funext J
    change _ * (r * f J) = r * (_ * f J)
    ring

/-- Each retained commutator is a dilation eigenvector
(BB (10.51)–(10.54), pp. 524–526). -/
theorem finiteDilate_truncatedBracket {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (I : List (Fin a)) :
    finiteDilate t (truncatedBracket I : WordCoefficients a s p) =
      t ^ wordWeight p I • truncatedBracket I := by
  have h := congrArg (restrict (a := a) (s := s) (p := p)) (dilate_formalBracket p t I)
  exact h

/-- Weighted dilation preserves the fixed Lie span (BB Proposition 10.48,
p. 526). -/
theorem finiteDilate_mem_formalSpan {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) {f : WordCoefficients a s p} (hf : f ∈ formalSpan a s p) :
    finiteDilate t f ∈ formalSpan a s p := by
  change dilationLinearMap t f ∈ formalSpan a s p
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨I, hne, hI, rfl⟩ := hg
    change finiteDilate t (truncatedBracket I) ∈ formalSpan a s p
    rw [finiteDilate_truncatedBracket]
    exact Submodule.smul_mem _ _ (truncatedBracket_mem_span I hne hI)
  | zero => simpa only [map_zero] using (formalSpan a s p).zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf

end RothschildStein.G3
