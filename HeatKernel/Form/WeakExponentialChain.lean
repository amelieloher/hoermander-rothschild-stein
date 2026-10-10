-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalExponentials
public import HeatKernel.Form.LocalWeakDerivatives
import Mathlib.Tactic.Linter

/-! # Weak horizontal chain rule for bounded local energy exponentials -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- The exponential of a bounded local energy function has the expected weak horizontal
first derivatives on the whole ambient open set. -/
theorem MemLocalEnergy.hasWeakWordDeriv_exp_bounded {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {ψ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy U X ψ) (hw : ∀ i, hasWeakWordDeriv X U [i] ψ (g i))
    {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖ψ x‖ ≤ A) (α : ℝ) (i : Fin q) :
    hasWeakWordDeriv X U [i] (fun x => Real.exp (α * ψ x))
      (fun x => α * Real.exp (α * ψ x) * g i x) := by
  apply hasWeakWordDeriv_of_precompact_restrictions U X [i]
  intro V hVc hVU
  obtain ⟨w, z, hwf, hzf, hzg⟩ := hψ.exists_exp_bounded_gradient U X hX hA hb α V hVc hVU
  have hwV := S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _)
    (energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) w.property i)
  have hgw : (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i :=
    S.hasWeakWordDeriv_unique X V
      (S.hasWeakWordDeriv_congr_ae X V hwV hwf EventuallyEq.rfl)
      (S.hasWeakWordDeriv_restrict X U V (subset_closure.trans hVU) (hw i))
  have hzV := S.hasWeakWordDeriv_restrict X ⊤ V (subset_univ _)
    (energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) z.property i)
  apply S.hasWeakWordDeriv_congr_ae X V hzV hzf
  filter_upwards [hzg i, hgw] with x hx hy
  rw [hx, hy]



end HeatKernel
