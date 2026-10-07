-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.SecondKernel

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem fourier_T1 (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    𝓕 (mollOp N δ hδ (DOp a i (DOp b k u))) ξ =
      ∫ α, ∫ β, tripleIntegrand a b u ξ (cT1 δ hδ i k ξ) (α, β) := by
  rw [fourier_mollOp, fourier_DOp]
  simp only [fourier_DOp, tripleIntegrand, cT1, ← integral_const_mul]
  congr 1; funext α; congr 1; funext β; ring

theorem fourier_T2 (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    𝓕 (DOp a i (mollOp N δ hδ (DOp b k u))) ξ =
      ∫ α, ∫ β, tripleIntegrand a b u ξ (cT2 δ hδ i k ξ) (α, β) := by
  rw [fourier_DOp]
  simp only [fourier_mollOp, fourier_DOp, tripleIntegrand, cT2, ← integral_const_mul]
  congr 1; funext α; congr 1; funext β; ring

theorem integrable_cT (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    Integrable (tripleIntegrand a b u ξ (cT1 δ hδ i k ξ)) (volume.prod volume) ∧
    Integrable (tripleIntegrand a b u ξ (cT2 δ hδ i k ξ)) (volume.prod volume) ∧
    Integrable (tripleIntegrand a b u ξ (cT3 δ hδ i k ξ)) (volume.prod volume) ∧
    Integrable (tripleIntegrand a b u ξ (cT4 δ hδ i k ξ)) (volume.prod volume) := by
  obtain ⟨c1, c2, c3, c4⟩ := continuous_cT δ hδ i k ξ
  have hC : 0 ≤ (4 * Real.pi * (1 + ‖ξ‖)) ^ 2 := by positivity
  have conv : ∀ α β : Carrier N, peetreOmega α ^ 2 * peetreOmega β ^ 2 =
      peetreOmega α ^ (2 : ℝ) * peetreOmega β ^ (2 : ℝ) := fun α β => by
    rw [Real.rpow_two, Real.rpow_two]
  refine ⟨integrable_tripleIntegrand a b u ξ _ c1 2 _ hC fun α β => ?_,
    integrable_tripleIntegrand a b u ξ _ c2 2 _ hC fun α β => ?_,
    integrable_tripleIntegrand a b u ξ _ c3 2 _ hC fun α β => ?_,
    integrable_tripleIntegrand a b u ξ _ c4 2 _ hC fun α β => ?_⟩
  · rw [← conv]; exact (norm_cT_le δ hδ i k ξ α β).1
  · rw [← conv]; exact (norm_cT_le δ hδ i k ξ α β).2.1
  · rw [← conv]; exact (norm_cT_le δ hδ i k ξ α β).2.2.1
  · rw [← conv]; exact (norm_cT_le δ hδ i k ξ α β).2.2.2

theorem fourier_T3 (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    𝓕 (DOp b k (mollOp N δ hδ (DOp a i u))) ξ =
      ∫ α, ∫ β, tripleIntegrand a b u ξ (cT3 δ hδ i k ξ) (α, β) := by
  have hI := (integrable_cT δ hδ a b u i k ξ).2.2.1
  rw [← integral_prod _ hI, integral_prod_symm _ hI, fourier_DOp]
  simp only [fourier_mollOp, fourier_DOp, tripleIntegrand, cT3, ← integral_const_mul]
  congr 1; funext β; congr 1; funext α
  rw [sub_right_comm ξ β α]
  ring

theorem fourier_T4 (δ : ℝ) (hδ : 0 < δ) (a b u : TestFunction N) (i k : Fin N) (ξ : Carrier N) :
    𝓕 (DOp b k (DOp a i (mollOp N δ hδ u))) ξ =
      ∫ α, ∫ β, tripleIntegrand a b u ξ (cT4 δ hδ i k ξ) (α, β) := by
  have hI := (integrable_cT δ hδ a b u i k ξ).2.2.2
  rw [← integral_prod _ hI, integral_prod_symm _ hI, fourier_DOp]
  simp only [fourier_mollOp, fourier_DOp, tripleIntegrand, cT4, ← integral_const_mul]
  congr 1; funext β; congr 1; funext α
  rw [sub_right_comm ξ β α]
  ring

end Hormander.B
