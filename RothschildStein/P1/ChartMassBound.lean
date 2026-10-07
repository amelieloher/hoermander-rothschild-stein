-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartKernelIntegrability

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The inverse input-chart Jacobian is uniformly
bounded on a compact endpoint patch. -/
theorem LiftedChart.exists_inverseJacobian_bound
    (C : LiftedChart w s Ω hΩ X x₀ m)
    (L : Set (Fin (n + m) → ℝ)) (hL : IsCompact L) (hLU : L ⊆ C.U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ ∈ L, ∀ η ∈ L,
      C.c ξ * (1 + C.ωm ξ (C.Θ η ξ)) ≤ B := by
  have hcU : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        C.c p.1 * (1 + C.ωm p.1 (C.Θ p.2 p.1))) (C.U ×ˢ C.U) :=
    ((C.density_smooth.continuousOn.comp continuousOn_fst
      (fun _ hp => hp.1)).mul
      (continuousOn_const.add C.contDiffOn_omegaMinus_theta.continuousOn))
  obtain ⟨B, hB⟩ := (hL.prod hL).exists_bound_of_continuousOn
    (hcU.mono (prod_mono hLU hLU))
  refine ⟨|B|, abs_nonneg B, ?_⟩
  intro ξ hξ η hη
  exact (le_abs_self _).trans ((hB (ξ, η) ⟨hξ, hη⟩).trans (le_abs_self B))

/-- Nonnegative model mass pulled back by the input
chart is bounded by its image mass times the inverse-Jacobian bound.
The measurable integration set may be a shell or a chart ball. -/
theorem LiftedChart.lintegral_comp_theta_le
    (C : LiftedChart w s Ω hΩ X x₀ m)
    (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ C.U)
    (S : Set (Fin (n + m) → ℝ)) (hS : MeasurableSet S) (hSU : S ⊆ C.U)
    (B : ℝ) (hB : ∀ η ∈ S, C.c ξ * (1 + C.ωm ξ (C.Θ η ξ)) ≤ B)
    (f : (Fin (n + m) → ℝ) → ℝ≥0∞) :
    (∫⁻ η in S, f (C.Θ η ξ)) ≤
      ENNReal.ofReal B * ∫⁻ u in (fun η => C.Θ η ξ) '' S, f u := by
  have hder : ∀ η ∈ S, HasFDerivWithinAt (fun η => C.Θ η ξ)
      (fderiv ℝ (fun η => C.Θ η ξ) η) S η :=
    fun η hη => (C.hasFDerivAt_Θ_fst hξ (hSU hη)).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder
    ((C.injOn_Θ_fst hξ).mono hSU) f, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hS
  intro η hη
  let δ := C.c ξ * (1 + C.ωm ξ (C.Θ η ξ))
  have hδ : 0 < δ := mul_pos (C.density_pos ξ hξ)
    (C.jacobian η (hSU hη) ξ hξ).2.1
  have hj := (C.jacobian η (hSU hη) ξ hξ).2.2.2
  rw [LiftedChart.absoluteJacobian_eq_abs_det] at hj
  have he : ENNReal.ofReal δ *
      ENNReal.ofReal |(fderiv ℝ (fun η => C.Θ η ξ) η).det| = 1 := by
    rw [← ENNReal.ofReal_mul hδ.le, hj]
    change ENNReal.ofReal (δ * δ⁻¹) = 1
    rw [mul_inv_cancel₀ hδ.ne', ENNReal.ofReal_one]
  calc
    f (C.Θ η ξ) = ENNReal.ofReal δ *
        (ENNReal.ofReal |(fderiv ℝ (fun η => C.Θ η ξ) η).det| * f (C.Θ η ξ)) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ ENNReal.ofReal B *
        (ENNReal.ofReal |(fderiv ℝ (fun η => C.Θ η ξ) η).det| * f (C.Θ η ξ)) :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (hB η hη)) _

end RothschildStein.P1
