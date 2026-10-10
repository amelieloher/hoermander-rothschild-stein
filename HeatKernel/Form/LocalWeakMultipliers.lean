-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalEnergy
import Mathlib.Tactic.Linter

/-! # Compact smooth products with local weak horizontal gradients -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- A local energy coefficient times a smooth compact function has the Leibniz gradient
with the specified local weak horizontal derivatives. -/
theorem MemLocalEnergy.exists_mul_smooth_compact_of_weakGradient {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hφ : MemLocalEnergy ⊤ X φ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (g i))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] (fun x => φ x * f x) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => φ x * fieldDerivative (X i) f x + g i x * f x) := by
  obtain ⟨V, w, z, hV, _, _, hwf, hzf, hzg⟩ :=
    hφ.exists_mul_smooth_compact_gradient ⊤ X hX hf hc (subset_univ _)
  have hwg : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      g i := by
    intro i
    have H := energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) w.property i
    have HV := S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) H
    exact S.hasWeakWordDeriv_unique X V
      (S.hasWeakWordDeriv_congr_ae X V HV hwf EventuallyEq.rfl)
      (S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _) (hw i))
  refine ⟨z, hzf, fun i => (hzg i).trans ?_⟩
  filter_upwards [ae_imp_of_ae_restrict (hwg i)] with x hx
  by_cases hzero : f x = 0
  · simp only [hzero, mul_zero, zero_add, add_zero]
  · rw [hx (hV (subset_tsupport f hzero)), add_comm]


end HeatKernel
