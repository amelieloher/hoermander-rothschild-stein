-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalGlobalConditional
public import RothschildStein.Definitions.memSobolevXLoc
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- solvability on all origin norm balls implies the exact
fixed local Sobolev membership of the actual group convolution. -/
theorem convolution_memSobolevXLoc_of_solutions {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (p : ℝ≥0∞)
    (F K : (Fin n → ℝ) → ℝ) (C : ℝ → List (Fin (q+1)) → ℝ)
    (hsol : ConvolutionLocalSolutions G H ν p F K C) :
    memSobolevXLoc driftWeight H.fields ⊤ 2 p (G2.groupConvolution G F K) := by
  intro U hcompact _
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn ν.gauge.1.continuousOn
  have hR : 0 < |B|+1 := by positivity
  obtain ⟨hu,_,_⟩ := hsol (|B|+1) hR
  apply S.memSobolevX_restrict driftWeight H.fields _ U _ hu
  intro x hx
  rw [quasiballDomain_origin_set]
  have hb := hB x (subset_closure hx)
  change ν x < |B|+1
  have hn : ν x ≤ B := (le_abs_self (ν x)).trans (by simpa only [Real.norm_eq_abs] using hb)
  linarith [le_abs_self B]

end RothschildStein.H3
