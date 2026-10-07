-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlHolderScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped NNReal ENNReal
namespace RothschildStein.H3

/-- Dilation changes the inhomogeneous Hölder norm by at
most max(1,R^alpha), on the exact inverse-image domain. -/
theorem holderNorm_dilate_le {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {R : ℝ} (hR : 0 < R) (a : ℝ≥0) (A : Set (ControlCarrier N))
    (f : ControlCarrier N → ℝ) :
    let _metric := gaugeMetric G ν h1 hsym
    H2.BoundedHolder a A f →
      H2.boundedHolderNorm a ((fun x : ControlCarrier N => G.dilate R x) ⁻¹' A)
        (fun x : ControlCarrier N => f (G.dilate R x)) ≤
      ENNReal.ofReal (max 1 (R ^ (a : ℝ))) * H2.boundedHolderNorm a A f := by
  let _metric := gaugeMetric G ν h1 hsym
  dsimp only
  intro hf
  obtain ⟨hs, hh⟩ := control_holderNorm_dilate G ν h1 hsym hR a A f hf.parts.2
  unfold H2.boundedHolderNorm
  rw [hs, hh]
  have h₁ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 (R ^ (a : ℝ))) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_left (1 : ℝ) _)
  have h₂ : ENNReal.ofReal (R ^ (a : ℝ)) ≤ ENNReal.ofReal (max 1 (R ^ (a : ℝ))) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  calc
    _ ≤ ENNReal.ofReal (max 1 (R ^ (a : ℝ))) * H2.holderSup A f +
        ENNReal.ofReal (max 1 (R ^ (a : ℝ))) * H2.holderSemi a A f :=
      add_le_add (by simpa only [one_mul] using mul_le_mul' h₁ (le_rfl : H2.holderSup A f ≤ _))
        (mul_le_mul' h₂ le_rfl)
    _ = _ := by rw [mul_add]

end RothschildStein.H3
