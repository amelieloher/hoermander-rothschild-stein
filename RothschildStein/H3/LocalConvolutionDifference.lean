-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalConvolutionExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
open scoped ENNReal
open G2

/-- The actual positive-type convolution is linear in the
source almost everywhere on each output ball, by absolute convergence. -/
theorem PositiveType.local_convolution_sub {n : ℕ} {G : HomogeneousGroup n}
    {α : ℝ} {T f g : (Fin n → ℝ) → ℝ} (hT : PositiveType G α T)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ₁ ρ₂ : ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) (hg : MemLp g p volume)
    (hsf : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0)
    (hsg : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → g y = 0) :
    groupConvolution G (f-g) T =ᵐ[volume.restrict {x | ν x < ρ₂}]
      groupConvolution G f T-groupConvolution G g T := by
  filter_upwards [hT.local_convolution_exists ν h1 hsym hp hf hsf,
    hT.local_convolution_exists ν h1 hsym hp hg hsg] with x hx hy
  simp only [Pi.sub_apply,groupConvolution_eq_integral,sub_mul]
  exact integral_sub hx hy

/-- The Young coefficient controls differences of convolutions on the
output ball, including both endpoint exponents. -/
theorem PositiveType.local_convolution_difference_bound {n : ℕ} {G : HomogeneousGroup n}
    {α : ℝ} {T f g : (Fin n → ℝ) → ℝ} (hT : PositiveType G α T)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) (hg : MemLp g p volume)
    (hsf : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0)
    (hsg : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → g y = 0) :
    eLpNorm (groupConvolution G f T-groupConvolution G g T) p
      (volume.restrict {x | ν x < ρ₂}) ≤
    ENNReal.ofReal (kernelSphereBound ν T * ((G.homogeneousDimension : ℝ) *
      (volume {x | ν x < 1}).toReal * (ρ₁+ρ₂)^α/α))*eLpNorm (f-g) p volume := by
  have hsub : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → (f-g) y = 0 := by
    filter_upwards [hsf,hsg] with y hy hz hr
    simp only [Pi.sub_apply,hy hr,hz hr,sub_self]
  rw [← eLpNorm_congr_ae (hT.local_convolution_sub ν h1 hsym hp hf hg hsf hsg)]
  exact (hT.local_convolution_bound ν h1 hsym hρ₁ hρ₂ hp (hf.sub hg) hsub).2

end RothschildStein.H3
