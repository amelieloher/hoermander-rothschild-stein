-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SymmetrizedForms
public import Mathlib.LinearAlgebra.Basis.VectorSpace
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- An injective tangent evaluation carries
an algebraic residual to a symmetric continuous ambient form, agreeing on
all tuples where that residual is already permutation invariant. -/
theorem exists_symmetric_form_on_invariant_tuples {U : Type*} [AddCommGroup U]
    [Module ℝ U] {N r : ℕ} (T : U →ₗ[ℝ] (Fin N → ℝ)) (hinj : Function.Injective T)
    (R : MultilinearMap ℝ (fun _ : Fin r => U) ℝ) :
    ∃ H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin N → ℝ) ℝ,
      (∀ (e : Equiv.Perm (Fin r)) (v : Fin r → (Fin N → ℝ)), H (fun i => v (e i)) = H v) ∧
      ∀ u : Fin r → U, (∀ e : Equiv.Perm (Fin r), R (fun i => u (e i)) = R u) →
        H (fun i => T (u i)) = R u := by
  obtain ⟨g,hg⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hleft : ∀ u, g (T u) = u := fun u => congrArg (fun L : Module.End ℝ U => L u) hg
  let R₀ := R.compLinearMap (fun _ => g)
  obtain ⟨H₀,hH₀⟩ := exists_continuous_form_of_multilinear R₀
  have hval : ∀ v : Fin r → (Fin N → ℝ), H₀ v = R (fun i => g (v i)) := by
    intro v
    exact congrArg (fun F => F v) hH₀
  refine ⟨symmetrizedForm H₀,symmetrizedForm_symmetric H₀,?_⟩
  intro u hu
  have hperm : ∀ e : Equiv.Perm (Fin r),
      H₀ (fun i => T (u (e i))) = H₀ (fun i => T (u i)) := by
    intro e
    rw [hval,hval]
    simp_rw [hleft]
    exact hu e
  rw [symmetrizedForm_eq_of_invariant H₀ (fun i => T (u i)) hperm,hval]
  simp_rw [hleft]
end RothschildStein.L1
