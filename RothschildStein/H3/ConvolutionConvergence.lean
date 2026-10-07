-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalConvolutionDifference
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
open scoped ENNReal Topology
open G2

/-- Source Lp convergence with common compact support gives local Lp
convergence to the positive-type convolution by the local kernel bounds. -/
theorem PositiveType.local_convolution_tendsto {n : ℕ} {G : HomogeneousGroup n}
    {α : ℝ} {T F : (Fin n → ℝ) → ℝ} (hT : PositiveType G α T)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ℕ → (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume) (hf : ∀ j, MemLp (f j) p volume)
    (hsF : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f j y = 0)
    (ht : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0)) :
    MemLp (groupConvolution G F T) p (volume.restrict {x | ν x < ρ₂}) ∧
      (∀ j, MemLp (groupConvolution G (f j) T) p (volume.restrict {x | ν x < ρ₂})) ∧
      Tendsto (fun j => eLpNorm (groupConvolution G (f j) T-groupConvolution G F T)
        p (volume.restrict {x | ν x < ρ₂})) atTop (𝓝 0) := by
  refine ⟨(hT.local_convolution_bound ν h1 hsym hρ₁ hρ₂ hp hF hsF).1,
    fun j => (hT.local_convolution_bound ν h1 hsym hρ₁ hρ₂ hp (hf j) (hsf j)).1,?_⟩
  let C := ENNReal.ofReal (kernelSphereBound ν T * ((G.homogeneousDimension : ℝ) *
    (volume {x | ν x < 1}).toReal * (ρ₁+ρ₂)^α/α))
  have htC : Tendsto (fun j => C*eLpNorm (f j-F) p volume) atTop (𝓝 0) := by
    simpa only [MulZeroClass.mul_zero] using ENNReal.Tendsto.const_mul (a := C) ht
      (Or.inr (show C ≠ ⊤ from ENNReal.ofReal_ne_top))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htC
    (fun _ => bot_le) (fun j => hT.local_convolution_difference_bound ν h1 hsym
      hρ₁ hρ₂ hp (hf j) hF (hsf j) hsF)

end RothschildStein.H3
