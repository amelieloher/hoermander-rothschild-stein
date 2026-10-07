-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectFreeness
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Analytic.IteratedFDeriv
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- A degree-r multilinear diagonal has zero
jets below r at the origin. -/
theorem iteratedFDeriv_multilinear_diagonal_zero {N r k : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ) (hk : k < r) :
    iteratedFDeriv ℝ k (fun x : Fin N → ℝ => H (fun _ => x)) 0 = 0 := by
  let g : (Fin N → ℝ) →L[ℝ] (Fin r → (Fin N → ℝ)) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Fin N → ℝ))
  have hz : iteratedFDeriv ℝ k H (0 : Fin r → (Fin N → ℝ)) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have he := H.norm_iteratedFDeriv_le k (0 : Fin r → (Fin N → ℝ))
    simpa only [Fintype.card_fin,norm_zero,zero_pow (by omega : r-k ≠ 0),mul_zero] using he
  change iteratedFDeriv ℝ k (H ∘ g) 0 = 0
  rw [g.iteratedFDeriv_comp_right (H.contDiff (n := (k : WithTop ℕ∞))) 0 le_rfl,map_zero,hz]
  ext v
  rfl

/-- Symmetry makes the top diagonal jet r! H. -/
theorem iteratedFDeriv_multilinear_diagonal_top {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ)
    (hsym : ∀ (e : Equiv.Perm (Fin r)) (v : Fin r → (Fin N → ℝ)),
      H (fun i => v (e i)) = H v) (x : Fin N → ℝ) :
    iteratedFDeriv ℝ r (fun y : Fin N → ℝ => H (fun _ => y)) x = (r.factorial : ℝ) • H := by
  ext v
  rw [H.iteratedFDeriv_comp_diagonal x v]
  simp_rw [hsym]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,
    smul_apply,smul_eq_mul]
end RothschildStein.L1
