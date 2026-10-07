-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetClasses
public import RothschildStein.L1.ConstantWordJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Actual coordinate partials are actual products of constant fields. -/
theorem rsPartial_eq_constant_wordDerivative {N : ℕ} (J : List (Fin N))
    (f : (Fin N → ℝ) → ℝ) :
    rsPartial J f = wordDerivative (fun j _ => Pi.single j (1 : ℝ)) J f := by
  induction J with
  | nil => rfl
  | cons j J ih =>
    simp only [rsPartial, wordDerivative]
    rw [ih]
    rfl

end RothschildStein.L1
