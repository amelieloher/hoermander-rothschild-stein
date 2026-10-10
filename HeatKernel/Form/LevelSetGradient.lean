-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroLevelGradient
public import HeatKernel.Form.ContinuouslyDifferentiableComposition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linter

/-! # Horizontal gradients vanish on every scalar level set -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Every horizontal derivative vanishes almost everywhere on each level set of an energy
function, including nonzero levels on spaces of infinite volume. -/
theorem energyGraph_gradient_zero_on_level {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    (c : ℝ) (i : Fin q) :
    ∀ᵐ x ∂volume, (u : GradientSpace (N := N) ⊤ q).fst x = c →
      (u : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
  by_cases hc : c = 0
  · simpa only [hc] using energyGraph_gradient_zero_on_zero X hX u i
  let k : ℝ := Real.pi / c
  have hk : k ≠ 0 := div_ne_zero Real.pi_ne_zero hc
  let η : ℝ → ℝ := fun s => Real.sin (k * s)
  have hη : ContDiff ℝ 1 η := Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hη0 : η 0 = 0 := by simp only [η, mul_zero, Real.sin_zero]
  have hd : ∀ s, deriv η s = Real.cos (k * s) * k := by
    intro s
    simpa only [η, mul_one, id_eq] using ((hasDerivAt_id s).const_mul k).sin.deriv
  have hb : ∀ s, ‖deriv η s‖ ≤ (‖k‖₊ : ℝ) := by
    intro s
    rw [hd, norm_mul, coe_nnnorm]
    have hcos : ‖Real.cos (k * s)‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (Real.abs_cos_le_one (k * s))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcos (norm_nonneg k)
  have hkc : k * c = Real.pi := div_mul_cancel₀ Real.pi hc
  have hηc : η c = 0 := by simp only [η, hkc, Real.sin_pi]
  have hdc : deriv η c = -k := by rw [hd, hkc, Real.cos_pi, neg_one_mul]
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_comp_contDiff_one X hX u hη hη0 hb
  filter_upwards [hzf, hzg i, energyGraph_gradient_zero_on_zero X hX z i] with x hf hg hz hx
  have hz0 : (z : GradientSpace (N := N) ⊤ q).fst x = 0 := by rw [hf, hx, hηc]
  have he := hz hz0
  rw [hg, hx, hdc] at he
  exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hk)



end HeatKernel
