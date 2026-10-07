-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.MultilinearDiagonalJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- The actual polynomial representing the diagonal of a multilinear form. -/
def multilinearDiagonalPolynomial {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ) : MvPolynomial (Fin N) ℝ :=
  ∑ q : Fin r → Fin N, MvPolynomial.C (H (fun i => Pi.single (q i) 1)) * ∏ i, MvPolynomial.X (q i)

/-- Expansion in standard coordinate vectors identifies the polynomial diagonal. -/
theorem eval_multilinearDiagonalPolynomial {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ) (x : Fin N → ℝ) :
    MvPolynomial.eval x (multilinearDiagonalPolynomial H) = H (fun _ => x) := by
  classical
  have hs : (∑ j, x j • Pi.single j (1 : ℝ)) = x := by
    convert Finset.univ_sum_single x using 1
    apply Finset.sum_congr rfl
    intro j _
    ext k
    by_cases h : j = k <;> simp [h]
  have he := H.toMultilinearMap.map_sum (fun (_ : Fin r) (j : Fin N) => x j • Pi.single j (1 : ℝ))
  rw [hs] at he
  simp only [MultilinearMap.map_smul_univ,smul_eq_mul] at he
  simp only [multilinearDiagonalPolynomial,MvPolynomial.eval_sum,map_mul,MvPolynomial.eval_C,
    MvPolynomial.eval_prod,MvPolynomial.eval_X]
  calc
    (∑ q : Fin r → Fin N, H (fun i => Pi.single (q i) 1) * ∏ i, x (q i)) =
        ∑ q : Fin r → Fin N, (∏ i, x (q i)) * H (fun i => Pi.single (q i) 1) := by
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := he.symm
end RothschildStein.L1
