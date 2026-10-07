-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCH
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The exponential product has linear part f+g (BB Lemma 9.69, p. 471). -/
theorem finiteExp_product_linear_order {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) :
    FiniteOrderAtLeast 2 (finiteExp f * finiteExp g - 1 - (f + g)) := by
  have he : finiteExp f * finiteExp g - 1 - (f + g) =
      expTail f + expTail g + (finiteExp f - 1) * (finiteExp g - 1) := by
    rw [finiteExp_eq f, finiteExp_eq g]
    noncomm_ring
  rw [he]
  exact finiteOrderAtLeast_add (finiteOrderAtLeast_add (expTail_order hf) (expTail_order hg))
    (finiteOrderAtLeast_mul (finiteExp_sub_one_order hf) (finiteExp_sub_one_order hg))

/-- C₁(f,g)=f+g: the nonlinear BCH correction starts at weighted order two
(BB Lemma 9.69, p. 471). -/
theorem finiteBCH_sub_add_order {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) : FiniteOrderAtLeast 2 (finiteBCH f g - (f + g)) := by
  have he : finiteBCH f g - (f + g) =
      (finiteExp f * finiteExp g - 1 - (f + g)) - expTail (finiteBCH f g) := by
    rw [← finiteExp_BCH hf hg, finiteExp_eq (finiteBCH f g)]
    abel
  rw [he]
  exact finiteOrderAtLeast_sub (finiteExp_product_linear_order hf hg)
    (expTail_order (finiteBCH_order hf hg))

end RothschildStein.G3
