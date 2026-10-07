-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.ComplexRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- restricting a locally integrable forcing
function's distribution gives the same function on the smaller open
set, preserving the exact test pairing. -/
theorem restrictComplexDistribution_ofFun {N : ℕ} (Ω U : Opens (Fin N → ℝ))
    (hU : U ≤ Ω) (g : (Fin N → ℝ) → ℂ)
    (hg : LocallyIntegrableOn g (Ω : Set (Fin N → ℝ)) volume) :
    restrictComplexDistribution Ω U (Distribution.ofFun Ω g volume (⊤ : ℕ∞)) =
      Distribution.ofFun U g volume (⊤ : ℕ∞) := by
  ext ψ
  rw [restrictComplexDistribution_apply Ω U hU,
    Distribution.ofFun_apply hg, Distribution.ofFun_apply (hg.mono_set hU)]
  rfl

end RothschildStein.Distribution
