-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SymmetricJetPolynomials
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- The continuous multilinear form with prescribed values on basis tuples. -/
def basisTupleForm {ι : Type*} [Fintype ι] {N r : ℕ}
    (b : Module.Basis ι ℝ (Fin N → ℝ)) (c : (Fin r → ι) → ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ :=
  ∑ q : Fin r → ι, c q • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap (fun i => (ContinuousLinearMap.proj (q i)).comp b.equivFunL.toContinuousLinearMap)

/-- Coordinate expansion of the form defined by a basis table. -/
theorem basisTupleForm_apply {ι : Type*} [Fintype ι] {N r : ℕ}
    (b : Module.Basis ι ℝ (Fin N → ℝ)) (c : (Fin r → ι) → ℝ)
    (v : Fin r → (Fin N → ℝ)) :
    basisTupleForm b c v = ∑ q : Fin r → ι, c q * ∏ i, b.equivFun (v i) (q i) := by
  classical
  simp [basisTupleForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- Any table on homogeneous basis tuples has
an actual continuous multilinear extension. -/
theorem basisTupleForm_on_basis {ι : Type*} [Fintype ι] {N r : ℕ}
    (b : Module.Basis ι ℝ (Fin N → ℝ)) (c : (Fin r → ι) → ℝ)
    (q : Fin r → ι) : basisTupleForm b c (fun i => b (q i)) = c q := by
  classical
  rw [basisTupleForm_apply]
  have hp : ∀ t : Fin r → ι, (∏ i, b.equivFun (b (q i)) (t i)) = if t = q then 1 else 0 := by
    intro t
    by_cases h : t = q
    · subst t
      simp [Module.Basis.equivFun_self]
    · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
      rw [ite_eq_right h]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Module.Basis.equivFun_self, Ne.symm hi]
  simp_rw [hp]
  simp
end RothschildStein.L1
