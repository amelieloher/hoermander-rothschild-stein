-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.HeatEvaluations

/-! # Integral representation from L² evaluation vectors

An almost-everywhere identification of a kernel row with its Riesz vector gives
an integrable representation for every L² input and every evaluation point.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- A kernel row represented by its Riesz vector belongs to L². -/
theorem memLp_evaluationKernel_of_ae_eq {n : ℕ}
    (L : ℝ → (Fin n → ℝ) → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ] ℝ)
    {t : ℝ} (x : Fin n → ℝ)
    (hrow : (fun y => evaluationKernel L t x y) =ᵐ[volume]
      (evaluationVector (L t) x : Lp ℝ 2 (volume : Measure (Fin n → ℝ)))) :
    MemLp (fun y => evaluationKernel L t x y) 2 volume :=
  (Lp.memLp (evaluationVector (L t) x)).ae_eq hrow.symm

/-- Pairing a represented kernel row with an L² input is integrable. -/
theorem integrable_evaluationKernel_mul_L2_of_ae_eq {n : ℕ}
    (L : ℝ → (Fin n → ℝ) → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ] ℝ)
    {t : ℝ} (x : Fin n → ℝ)
    (hrow : (fun y => evaluationKernel L t x y) =ᵐ[volume]
      (evaluationVector (L t) x : Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    Integrable (fun y => evaluationKernel L t x y * f y) volume := by
  have h : Integrable (fun y => evaluationVector (L t) x y * f y) volume := by
    simpa [mul_comm] using L2.integrable_inner (𝕜 := ℝ) (evaluationVector (L t) x) f
  apply h.congr
  filter_upwards [hrow] with y hy
  rw [hy]

/-- Every represented kernel row reproduces its bounded evaluation on all L² inputs. -/
theorem integral_evaluationKernel_mul_L2_of_ae_eq {n : ℕ}
    (L : ℝ → (Fin n → ℝ) → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ] ℝ)
    {t : ℝ} (x : Fin n → ℝ)
    (hrow : (fun y => evaluationKernel L t x y) =ᵐ[volume]
      (evaluationVector (L t) x : Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    ∫ y, evaluationKernel L t x y * f y = L t x f := by
  calc
    ∫ y, evaluationKernel L t x y * f y =
        ∫ y, evaluationVector (L t) x y * f y := by
      apply integral_congr_ae
      filter_upwards [hrow] with y hy
      rw [hy]
    _ = inner ℝ (evaluationVector (L t) x) f := by
      simp [L2.inner_def, mul_comm]
    _ = L t x f := inner_evaluationVector (L t) x f

end HeatKernel
