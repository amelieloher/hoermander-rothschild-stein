-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.CoordinatePartialSuccessor
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N}

/-- Coordinate expansion of a scalar directional derivative on the actual
finite-dimensional carrier. No regularity assumption is needed for this linear identity. -/
theorem fieldDerivative_coordinate_sum (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    fieldDerivative Y f u = ∑ j, Y u j * fderiv ℝ f u (Pi.single j 1) := by
  classical
  unfold fieldDerivative
  conv_lhs => arg 2; rw [pi_eq_sum_univ' (Y u)]
  simp

/-- The model derivative is the actual finite
sum of differentiated coefficients and successor derivatives of the pole.
This uses only punctured smoothness of Γ (BB Lemma 11.18, p. 549). -/
theorem PrincipalTerm.modelKernel_coordinate_derivative (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin N → ℝ)}ᶜ)
    (ξ η u : Fin N → ℝ) (hu : u ≠ 0) (j : Fin N) :
    fderiv ℝ (t.modelKernel ξ η) u (Pi.single j 1) =
      ∑ α ∈ t.indices,
        (fderiv ℝ ((t.D ξ η).coefficient α) u (Pi.single j 1) *
            euclideanPartial α (F.pole t.star) u +
          (t.D ξ η).coefficient α u *
            euclideanPartial (α + Pi.single j 1) (F.pole t.star) u) := by
  classical
  have hp (α : Fin N → ℕ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (euclideanPartial α (F.pole t.star)) {(0 : Fin N → ℝ)}ᶜ := by
    apply contDiffOn_iff_forall_nat_le.mpr
    intro m _
    exact H1.contDiffOn_euclideanPartial_finite
      ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩ α m (F.pole t.star)
      (hΓ.of_le (by simp))
  have hd (α : Fin N → ℕ) : DifferentiableAt ℝ
      (euclideanPartial α (F.pole t.star)) u :=
    ((hp α).contDiffAt (isOpen_compl_singleton.mem_nhds hu)).differentiableAt (by simp)
  have hc (α : Fin N → ℕ) (hα : α ∈ t.indices) :
      DifferentiableAt ℝ ((t.D ξ η).coefficient α) u :=
    ((t.D ξ η).smooth_coefficient α (by rw [t.indices_eq]; exact hα)).differentiable
      (by simp) |>.differentiableAt
  have he : t.modelKernel ξ η = (fun v => ∑ α ∈ t.indices,
      (t.D ξ η).coefficient α v * euclideanPartial α (F.pole t.star) v) := by
    funext v
    simp only [PrincipalTerm.modelKernel, SmoothDifferentialOperator.apply, t.indices_eq]
  rw [he]
  have hs := fderiv_fun_sum (A := fun α v =>
    (t.D ξ η).coefficient α v * euclideanPartial α (F.pole t.star) v)
    (fun α hα => (hc α hα).mul (hd α))
  rw [hs]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro α hα
  rw [fderiv_fun_mul (hc α hα) (hd α)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [euclideanPartial_coordinate_successor_local
    ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩ α j (F.pole t.star) hΓ u hu]
  ring

end RothschildStein.P1
