-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearFieldDerivative
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- A bounded coefficient vector and bounded actual fields
give a uniform bound for the coefficient-linear field itself (BB p. 452). -/
theorem norm_parameter_linear_field_le {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : Fin m → E → E)
    (p : (Fin m → ℝ) × E) {A M : ℝ} (hA : 0 ≤ A)
    (hcoef : ‖p.1‖ ≤ A) (hY : ∀ J, ‖Y J p.2‖ ≤ M) :
    ‖∑ J, p.1 J • Y J p.2‖ ≤ (m : ℝ) * A * M := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _J : Fin m, A * M := by
      apply Finset.sum_le_sum
      intro J _hJ
      rw [norm_smul]
      exact mul_le_mul ((norm_le_pi_norm p.1 J).trans hcoef) (hY J) (norm_nonneg _) hA
    _ = (m : ℝ) * A * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The actual full coefficient/state derivative of a finite
linear field has a uniform operator bound from field values, spatial
first derivatives and coefficient size. Both parameter forcing and
spatial transport terms are retained (BB p. 452). -/
theorem norm_parameter_linear_field_state_fderiv_le {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : Fin m → E → E)
    (p : (Fin m → ℝ) × E) {A D M : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hcoef : ‖p.1‖ ≤ A) (hY : ∀ J, ‖Y J p.2‖ ≤ M)
    (hDY : ∀ J, ‖fderiv ℝ (Y J) p.2‖ ≤ D)
    (hDiff : ∀ J, DifferentiableAt ℝ (Y J) p.2) :
    ‖fderiv ℝ (fun q : (Fin m → ℝ) × E => ∑ J, q.1 J • Y J q.2) p‖ ≤
      (m : ℝ) * (A * D + M) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [linear_field_family_fderiv Y p z hDiff]
  apply (norm_sum_le _ _).trans
  have hsum : ∀ J : Fin m,
      ‖p.1 J • fderiv ℝ (Y J) p.2 z.2 + z.1 J • Y J p.2‖ ≤ (A * D + M) * ‖z‖ := by
    intro J
    have hpc : ‖p.1 J‖ ≤ A := (norm_le_pi_norm p.1 J).trans hcoef
    have hzc : ‖z.1 J‖ ≤ ‖z‖ := (norm_le_pi_norm z.1 J).trans (norm_fst_le z)
    have hd : ‖fderiv ℝ (Y J) p.2 z.2‖ ≤ D * ‖z‖ :=
      ((fderiv ℝ (Y J) p.2).le_opNorm _).trans
        (mul_le_mul (hDY J) (norm_snd_le z) (norm_nonneg _) hD)
    calc
      _ ≤ ‖p.1 J • fderiv ℝ (Y J) p.2 z.2‖ + ‖z.1 J • Y J p.2‖ := norm_add_le _ _
      _ = ‖p.1 J‖ * ‖fderiv ℝ (Y J) p.2 z.2‖ + ‖z.1 J‖ * ‖Y J p.2‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ A * (D * ‖z‖) + ‖z‖ * M := add_le_add
        (mul_le_mul hpc hd (norm_nonneg _) hA)
        (mul_le_mul hzc (hY J) (norm_nonneg _) (norm_nonneg _))
      _ = (A * D + M) * ‖z‖ := by ring
  calc
    _ ≤ ∑ _J : Fin m, (A * D + M) * ‖z‖ := Finset.sum_le_sum (fun J _ => hsum J)
    _ = (m : ℝ) * (A * D + M) * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end RothschildStein.G4
