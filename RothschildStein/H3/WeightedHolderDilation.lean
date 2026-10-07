-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlHolderScaling
public import RothschildStein.H2.HolderLinear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Exact full-norm scaling of a weighted jet, keeping
supremum and seminorm separate (BB Corollary 8.51, p. 380). -/
theorem weighted_holderNorm_dilate {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {R : ℝ} (hR : 0 < R) (degree : ℝ) (a : ℝ≥0)
    (f : ControlCarrier N → ℝ) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    H2.holderSemi a univ f < ⊤ →
      @H2.boundedHolderNorm (ControlCarrier N) metric a univ
        (fun x : ControlCarrier N => R ^ degree * f (G.dilate R x)) =
        ENNReal.ofReal (R ^ degree) * (H2.holderSup univ f +
          ENNReal.ofReal (R ^ (a : ℝ)) * H2.holderSemi a univ f) := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hf
  obtain ⟨hs, hh⟩ := control_holderNorm_dilate G ν h1 hsym hR a univ f hf
  have he : (fun x : ControlCarrier N => R ^ degree * f (G.dilate R x)) =
      (R ^ degree) • (fun x : ControlCarrier N => f (G.dilate R x)) := by
    funext x
    rfl
  have hn := @H2.boundedHolderNorm_smul (ControlCarrier N) metric a univ
    (R ^ degree) (fun x : ControlCarrier N => f (G.dilate R x))
  have hn' := (congrArg (@H2.boundedHolderNorm (ControlCarrier N) metric a univ) he).trans hn
  rw [abs_of_pos (Real.rpow_pos_of_pos hR degree)] at hn'
  simp only [Set.preimage_univ] at hs hh
  have hb : H2.boundedHolderNorm a univ (fun x : ControlCarrier N => f (G.dilate R x)) =
      H2.holderSup univ f + ENNReal.ofReal (R ^ (a : ℝ)) * H2.holderSemi a univ f :=
    congrArg₂ (fun x y : ℝ≥0∞ => x + y) hs hh
  exact hn'.trans (congrArg (ENNReal.ofReal (R ^ degree) * ·) hb)

end RothschildStein.H3
