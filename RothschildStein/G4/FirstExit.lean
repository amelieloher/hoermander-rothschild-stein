-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ConstantControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- Every intermediate point remains in the Euclidean buffer if
control cost times the field bound is smaller than its radius. This uses
only first exit, so the field bound is needed only inside the buffer
(BB Proposition 9.7, p. 403). -/
theorem controlledCurve_stays_ball {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ B R : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w Z δ γ)
    (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : δ * B < R)
    (hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖Z i z‖ ≤ B) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball (γ 0) R := by
  intro t ht
  rw [mem_ball, dist_eq_norm]
  by_cases ht0 : t = 0
  · subst t
    simpa using hR
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hsub := G1.isControlledCurve_comp_affine (c := 0) (d := t) hγ hγ.1 ht0
      (fun v hv => by constructor <;> dsimp <;> nlinarith [hv.1, hv.2, ht.1, ht.2])
      (fun i => by rw [abs_of_pos htp]; exact mul_le_of_le_one_left (pow_nonneg hγ.1.le _) ht.2)
    by_contra hbad
    have hex := G1.controlledCurve_firstExit_bound hsub hδ1 hB hR
      (by simpa only [mul_one, mul_zero, add_zero, zero_add] using le_of_not_gt hbad)
      (by simpa only [mul_zero, add_zero, zero_add] using hbound)
    exact (not_le_of_gt hsmall) hex

/-- The same buffer yields the quantitative displacement at every
time, without a global bound on the ambient-domain coefficients
(BB Proposition 9.7, p. 403). -/
theorem controlledCurve_displacement_le_in_buffer {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ B R : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w Z δ γ)
    (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hR : 0 < R) (hsmall : δ * B < R)
    (hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖Z i z‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖γ t - γ 0‖ ≤ δ * B := by
  have hstay := controlledCurve_stays_ball hγ hδ1 hB hR hsmall hbound
  have hd := G1.controlledCurve_initial_displacement_le hγ hδ1 hB ht
    (fun v hv => hbound (γ v) (le_of_lt (by
      simpa only [mem_ball, dist_eq_norm] using hstay v ⟨hv.1, hv.2.trans ht.2⟩)))
  exact hd.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hγ.1.le hB))

end RothschildStein.G4
