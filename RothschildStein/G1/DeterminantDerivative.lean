-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G1

/-- Jacobi's determinant differential identity along a matrix solution
`M' = A M`, including singular matrices and dimension zero. It follows by
multilinearity in the rows (BB Prop 2.22, pp. 89–90). -/
theorem matrixODE_det_hasDerivAt {N : ℕ} {M : ℝ → Matrix (Fin N) (Fin N) ℝ}
    {A : Matrix (Fin N) (Fin N) ℝ} {t : ℝ}
    (hM : HasDerivAt M (A * M t) t) :
    HasDerivAt (fun v => (M v).det) (A.trace * (M t).det) t := by
  let D : ContinuousMultilinearMap ℝ (fun _ : Fin N => Fin N → ℝ) ℝ :=
    { Matrix.detRowAlternating.toMultilinearMap with cont := continuous_id.matrix_det }
  have hd := (D.hasFDerivAt (M t)).comp_hasDerivAt t hM
  have heq : D.linearDeriv (M t) (A * M t) = A.trace * (M t).det := by
    change D.linearDeriv (fun i j => M t i j) (fun i j => (A * M t) i j) = _
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, ((M t).updateRow i ((A * M t) i)).det) = _
    have hrow : ∀ i, (A * M t) i = ∑ k, A i k • M t k := by
      intro i
      ext j
      simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
    rw [← Finset.sum_mul]
    rfl
  change HasDerivAt (fun v => (M v).det) (D.linearDeriv (M t) (A * M t)) t at hd
  rwa [heq] at hd

end RothschildStein.G1
