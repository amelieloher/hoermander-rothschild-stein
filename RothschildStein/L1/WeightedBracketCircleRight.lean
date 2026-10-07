-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedCircleAction
public import RothschildStein.L1.WeightedFieldLinear
public import RothschildStein.L1.WeightedFieldLocality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The saved ordinary order also holds with the circle field on the right. -/
theorem fieldJetClass_lieBracket_circle_right {N p : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    {ω : Fin N → ℕ} {a b : ℝ} {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    (hV : fieldJetClass Ω ω a p V) (hW : circleFieldJetClass Ω ω b (p+1) W) :
    fieldJetClass Ω ω (a+b) p (VectorField.lieBracket ℝ V W) := by
  have hh := fieldJetClass_const_smul Ω h0
    (fieldJetClass_lieBracket_circle Ω h0 hW hV) (-1)
  have hn : fieldJetClass Ω ω (a+b) p
      (fun u => -VectorField.lieBracket ℝ W V u) := by
    simpa only [neg_one_smul,add_comm] using hh
  apply fieldJetClass_congr Ω h0 hn
  intro u _
  exact VectorField.lieBracket_swap
end RothschildStein.L1
