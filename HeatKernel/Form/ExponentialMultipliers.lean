-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BoundedWeakMultipliers
public import HeatKernel.Form.WeakExponentialChain
import Mathlib.Tactic.Linter

/-! # Exponential multipliers on the global horizontal energy domain -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- Exponentials of bounded local energy functions with bounded horizontal gradients multiply
the global energy domain, with the full horizontal Leibniz rule. -/
theorem exists_energyGraph_mul_exp_bounded_local {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {ψ : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy ⊤ X ψ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] ψ (g i))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume, ‖ψ x‖ ≤ A) (hgb : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ B) (α : ℝ) :
    ∃ z : energyGraph (N := N) ⊤ X,
      ((z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => Real.exp (α * ψ x) * (u : GradientSpace (N := N) ⊤ q).fst x)) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => Real.exp (α * ψ x) * (u : GradientSpace (N := N) ⊤ q).snd i x +
          (α * Real.exp (α * ψ x) * g i x) * (u : GradientSpace (N := N) ⊤ q).fst x) := by
  have hb' : ∀ᵐ x ∂volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)), ‖ψ x‖ ≤ A := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hb
  have hwe := hψ.hasWeakWordDeriv_exp_bounded ⊤ X hX hw hA hb' α
  have he : ∀ᵐ x ∂volume, ‖Real.exp (α * ψ x)‖ ≤ Real.exp (|α| * A) := by
    filter_upwards [hb] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    calc
      α * ψ x ≤ |α * ψ x| := le_abs_self _
      _ = |α| * ‖ψ x‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ |α| * A := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hgeb : ∀ i, ∀ᵐ x ∂volume, ‖α * Real.exp (α * ψ x) * g i x‖ ≤
      |α| * Real.exp (|α| * A) * B := by
    intro i
    filter_upwards [he, hgb i] with x hx hy
    simp only [norm_mul, Real.norm_eq_abs] at hx ⊢
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    · simpa only [Real.norm_eq_abs] using hy
    · exact abs_nonneg _
    · exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  exact exists_energyGraph_mul_bounded_local X hX u (hψ.exp_bounded ⊤ X hX hA hb' α)
    hwe (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hB) he hgeb



end HeatKernel
