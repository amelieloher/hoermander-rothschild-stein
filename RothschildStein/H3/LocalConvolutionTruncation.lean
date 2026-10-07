-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.BoundedTypeKernel
public import RothschildStein.G2.ConvolutionSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- On the output ball a compactly supported input sees only the
kernel ball of radius ρ1+ρ2, exactly. AE input support is sufficient. -/
theorem groupConvolution_eq_boundedKernel (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {f T : (Fin N → ℝ) → ℝ}
    {ρ₁ ρ₂ : ℝ} (hf : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0)
    {x : Fin N → ℝ} (hx : ν x < ρ₂) :
    groupConvolution G f T x = groupConvolution G f (boundedTypeKernel ν T (ρ₁ + ρ₂)) x := by
  rw [groupConvolution_eq_integral, groupConvolution_eq_integral]
  apply integral_congr_ae
  filter_upwards [hf] with y hy
  by_cases hy0 : f y = 0
  · rw [hy0]
    ring
  · have hyr : ν y < ρ₁ := lt_of_not_ge (fun he => hy0 (hy he))
    have hdist : ν (G.mul (G.inv y) x) ≤ ρ₁ + ρ₂ := by
      have hb := ν.mul_le (G.inv y) x
      rw [h1, one_mul, hsym y] at hb
      exact (hb.trans_lt (add_lt_add hyr hx)).le
    have hmem : G.mul (G.inv y) x ∈ {z | ν z ≤ ρ₁ + ρ₂} := hdist
    rw [boundedTypeKernel, indicator_of_mem hmem]

/-- The same truncation identity holds for absolute convergence
of the defining integrands on the output ball. -/
theorem groupConvolutionExistsAt_boundedKernel_iff (ν : HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) {f T : (Fin N → ℝ) → ℝ}
    {ρ₁ ρ₂ : ℝ} (hf : ∀ᵐ y ∂volume, ρ₁ ≤ ν y → f y = 0)
    {x : Fin N → ℝ} (hx : ν x < ρ₂) :
    GroupConvolutionExistsAt G f T x ↔
      GroupConvolutionExistsAt G f (boundedTypeKernel ν T (ρ₁ + ρ₂)) x := by
  apply integrable_congr
  filter_upwards [hf] with y hy
  by_cases hy0 : f y = 0
  · rw [hy0]
    ring
  · have hyr : ν y < ρ₁ := lt_of_not_ge (fun he => hy0 (hy he))
    have hdist : ν (G.mul (G.inv y) x) ≤ ρ₁ + ρ₂ := by
      have hb := ν.mul_le (G.inv y) x
      rw [h1, one_mul, hsym y] at hb
      exact (hb.trans_lt (add_lt_add hyr hx)).le
    have hmem : G.mul (G.inv y) x ∈ {z | ν z ≤ ρ₁ + ρ₂} := hdist
    rw [boundedTypeKernel, indicator_of_mem hmem]

end RothschildStein.H3
