-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalLogarithmicGradient
public import HeatKernel.Sobolev.LowerTruncatedRealPower
import Mathlib.Tactic

/-! # Weak gradients of positive shifts of nonnegative local energy functions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

variable {N q : ℕ} {U : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    {g : Fin q → (Fin N → ℝ) → ℝ} (hg : ∀ i, hasWeakWordDeriv X U [i] f (g i))

include hX hf hg

/-- Adding a constant preserves the supplied local weak gradient. -/
theorem MemLocalEnergy.add_const_with_weak_gradient (c : ℝ) :
    MemLocalEnergy U X (fun x => f x + c) ∧
      ∀ i, hasWeakWordDeriv X U [i] (fun x => f x + c) (g i) := by
  have hLip : LipschitzWith 1 (fun s : ℝ => s + c) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [NNReal.coe_one, one_mul, dist_add_right]
    exact le_rfl
  have hη : ∀ s ∉ (∅ : Set ℝ), ContDiffAt ℝ 1 (fun t : ℝ => t + c) s := by
    intro s _
    exact (contDiff_id.add contDiff_const).contDiffAt
  have hd : ∀ s ∉ (∅ : Set ℝ), (1 : ℝ) = deriv (fun t : ℝ => t + c) s := by
    intro s _
    exact ((hasDerivAt_id s).add_const c).deriv.symm
  simpa only [Function.comp_def, one_mul] using
    hf.comp_piecewise_with_weak_gradient hX hg hLip ∅ countable_empty hη hd

/-- Every positive shift of a nonnegative local energy function has the literal
logarithmic weak gradient for the original supplied derivative. -/
theorem MemLocalEnergy.log_add_const_with_weak_gradient
    (hnonneg : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    MemLocalEnergy U X (fun x => Real.log (f x + ε)) ∧
      ∀ i, hasWeakWordDeriv X U [i] (fun x => Real.log (f x + ε))
        (fun x => g i x / (f x + ε)) := by
  obtain ⟨hs, hgs⟩ := hf.add_const_with_weak_gradient hX hg ε
  apply hs.log_with_weak_gradient_of_ae_lower_bound hX hgs hε
  filter_upwards [hnonneg] with x hx
  exact le_add_of_nonneg_left hx

end HeatKernel
