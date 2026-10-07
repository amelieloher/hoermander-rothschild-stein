-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.NestedCutoffs
public import RothschildStein.H1.ShellDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: a smooth compact cutoff equals one on an inner
gauge ball and vanishes outside the unit ball. The gauge itself only
needs to be continuous (BB Corollary 6.31, p. 280). -/
theorem exists_smoothShellCutoff {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {a : ℝ} (ha : a < 1) :
    ∃ η : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x, ν x ≤ a → η x = 1) ∧
      (∀ x, 1 ≤ ν x → η x = 0) := by
  let U : Opens (Fin N → ℝ) := ⟨{x | ν x < 1}, isOpen_lt hν.1 continuous_const⟩
  have hK := G2.isCompact_gauge_le hν a
  obtain ⟨η, W, _, hKW, he, hb⟩ := exists_test_eq_one_near_compact U hK
    (by intro x hx; exact hx.trans_lt ha)
  refine ⟨η, η.contDiff, η.hasCompactSupport, hb, ?_, ?_⟩
  · intro x hx
    exact he x (hKW hx)
  · intro x hx
    exact η.zero_on_compl (not_lt_of_ge hx)

end RothschildStein.H1
