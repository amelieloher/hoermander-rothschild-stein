-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ContinuousFormRealization
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- Average an actual continuous multilinear form over argument permutations. -/
def symmetrizedForm {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ :=
  (Fintype.card (Equiv.Perm (Fin r)) : ℝ)⁻¹ • ∑ e : Equiv.Perm (Fin r), H.domDomCongr e

/-- Evaluation of the averaged form. -/
theorem symmetrizedForm_apply {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ)
    (v : Fin r → (Fin N → ℝ)) :
    symmetrizedForm H v = (Fintype.card (Equiv.Perm (Fin r)) : ℝ)⁻¹ *
      ∑ e : Equiv.Perm (Fin r), H (fun i => v (e i)) := by
  classical
  simp only [symmetrizedForm,smul_apply,smul_eq_mul,sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

/-- Averaging produces an exactly symmetric
continuous form, including order zero. -/
theorem symmetrizedForm_symmetric {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ)
    (σ : Equiv.Perm (Fin r)) (v : Fin r → (Fin N → ℝ)) :
    symmetrizedForm H (fun i => v (σ i)) = symmetrizedForm H v := by
  classical
  rw [symmetrizedForm_apply,symmetrizedForm_apply]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft σ)
  intro e
  rfl

/-- On any tuple where the original residual is already permutation
invariant, symmetrization preserves its value exactly. -/
theorem symmetrizedForm_eq_of_invariant {N r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ)
    (v : Fin r → (Fin N → ℝ))
    (hv : ∀ e : Equiv.Perm (Fin r), H (fun i => v (e i)) = H v) :
    symmetrizedForm H v = H v := by
  classical
  rw [symmetrizedForm_apply]
  simp_rw [hv]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast
    (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin r)) ≠ 0)),one_mul]
end RothschildStein.L1
