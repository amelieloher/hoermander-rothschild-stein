-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Preservation of real subspaces by polynomial operator limits

A complex operator preserving a real subspace has the same property for every real
polynomial in that operator. Closedness passes this property to operator limits.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem mapsTo_pow_of_mapsTo (S : Submodule ℝ E) (T : E →L[ℂ] E)
    (hT : MapsTo T S S) (n : ℕ) : MapsTo (T ^ n) S S := by
  induction n with
  | zero =>
    intro x hx
    exact hx
  | succ n hn =>
    intro x hx
    simpa only [pow_succ', mul_apply_eq_comp] using hT (hn hx)

theorem mapsTo_aeval_of_mapsTo (S : Submodule ℝ E) (T : E →L[ℂ] E)
    (hT : MapsTo T S S) (p : Polynomial ℝ) : MapsTo (Polynomial.aeval T p) S S := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    change ((Polynomial.aeval T) (p + q)) x ∈ S
    rw [map_add, add_apply]
    exact S.add_mem (hp hx) (hq hx)
  | monomial n a =>
    intro x hx
    change ((Polynomial.aeval T) (Polynomial.monomial n a)) x ∈ S
    rw [Polynomial.aeval_monomial, mul_apply_eq_comp, ContinuousLinearMap.algebraMap_apply]
    exact S.smul_mem a (mapsTo_pow_of_mapsTo S T hT n hx)

end HeatKernel
