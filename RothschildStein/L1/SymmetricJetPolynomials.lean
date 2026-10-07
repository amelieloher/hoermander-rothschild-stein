-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.MultilinearPolynomials
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Every symmetric r-form is the top jet of
an actual polynomial whose lower jets vanish (BB (10.14), pp. 496–498). -/
theorem exists_polynomial_with_symmetric_top_jet {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin r)) (v : Fin r → (Fin N → ℝ)),
      H (fun i => v (e i)) = H v) :
    ∃ u : MvPolynomial (Fin N) ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u) ∧
      (∀ k < r, iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x u) 0 = 0) ∧
      iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x u) 0 = H := by
  let H₀ := (r.factorial : ℝ)⁻¹ • H
  have hsym₀ : ∀ (e : Equiv.Perm (Fin r)) (v : Fin r → (Fin N → ℝ)),
      H₀ (fun i => v (e i)) = H₀ v := by
    intro e v
    change (r.factorial : ℝ)⁻¹ * H (fun i => v (e i)) = (r.factorial : ℝ)⁻¹ * H v
    rw [hsym]
  have hfun : (fun x => MvPolynomial.eval x (multilinearDiagonalPolynomial H₀)) =
      (fun x : Fin N → ℝ => H₀ (fun _ => x)) := funext (eval_multilinearDiagonalPolynomial H₀)
  refine ⟨multilinearDiagonalPolynomial H₀,?_,?_,?_⟩
  · rw [hfun]
    exact H₀.contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))
  · intro k hk
    rw [hfun]
    exact iteratedFDeriv_multilinear_diagonal_zero H₀ hk
  · rw [hfun,iteratedFDeriv_multilinear_diagonal_top H₀ hsym₀]
    change (r.factorial : ℝ) • ((r.factorial : ℝ)⁻¹ • H) = H
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero r)),one_smul]
end RothschildStein.L1
