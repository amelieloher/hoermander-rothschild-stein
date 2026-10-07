-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalConvolutionBound
public import RothschildStein.G2.YoungAbsolute

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- The original convolution is absolutely convergent almost everywhere
in the output ball for every Young(p,1,p) exponent, including endpoints. -/
theorem PositiveType.local_convolution_exists {α : ℝ} {T f : (Fin N → ℝ) → ℝ}
    (hT : PositiveType G α T) (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {ρ₁ ρ₂ : ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p volume) (hsupp : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0) :
    ∀ᵐ x ∂volume.restrict {x | ν x < ρ₂}, GroupConvolutionExistsAt G f T x := by
  have hk := memLp_one_iff_integrable.mpr (hT.boundedKernel_integrable ν.gauge (ρ₁ + ρ₂))
  have he : p⁻¹ + (1 : ℝ≥0∞)⁻¹ = 1 + p⁻¹ := by simp only [inv_one, add_comm]
  have H := groupConvolutionExistsAt_ae_extended G hp le_rfl hp he hf hk
  filter_upwards [ae_restrict_of_ae H,
    ae_restrict_mem (isOpen_lt ν.gauge.1 continuous_const).measurableSet] with x hx hxball
  exact (groupConvolutionExistsAt_boundedKernel_iff ν h1 hsym hsupp hxball).mpr hx

end RothschildStein.H3
