-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.BasisMultilinearForms
public import Mathlib.LinearAlgebra.Multilinear.Basis
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- An algebraic multilinear scalar form
on a finite coordinate space has an exact continuous realization. -/
theorem exists_continuous_form_of_multilinear {N r : ℕ}
    (R : MultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ) :
    ∃ H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ,
      H.toMultilinearMap = R := by
  let b : Module.Basis (Fin N) ℝ (Fin N → ℝ) := Pi.basisFun ℝ (Fin N)
  let c : (Fin r → Fin N) → ℝ := fun q => R (fun i => b (q i))
  refine ⟨basisTupleForm b c,?_⟩
  apply Module.Basis.ext_multilinear (fun _ => b)
  intro q
  exact basisTupleForm_on_basis b c q
end RothschildStein.L1
