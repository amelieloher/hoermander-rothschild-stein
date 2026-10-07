-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldLinear
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Addition preserves a fixed weighted field jet class. -/
theorem fieldJetClass_add {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {R S : (Fin N → ℝ) → (Fin N → ℝ)} (hR : fieldJetClass Ω ω a p R)
    (hS : fieldJetClass Ω ω a p S) : fieldJetClass Ω ω a p (fun u => R u + S u) := by
  refine ⟨hR.1.add hS.1, ?_⟩
  intro j
  exact (scalarJetClass_add Ω h0
    (show scalarJetClass Ω ω (a + ω j) p (fun u => R u j) from
      ⟨contDiffOn_pi.mp hR.1 j, hR.2 j⟩)
    (show scalarJetClass Ω ω (a + ω j) p (fun u => S u j) from
      ⟨contDiffOn_pi.mp hS.1 j, hS.2 j⟩)).2

/-- Each component of a circle field retains its shifted circle weight. -/
theorem circleScalarJetClass_coordinate_of_circleField {N p : ℕ}
    {Ω : Set (Fin N → ℝ)} {ω : Fin N → ℕ} {a : ℝ}
    {R : (Fin N → ℝ) → (Fin N → ℝ)}
    (hR : circleFieldJetClass Ω ω a p R) (j : Fin N) :
    circleScalarJetClass Ω ω (a + ω j) p (fun u => R u j) := by
  refine ⟨⟨contDiffOn_pi.mp hR.1.1 j, hR.1.2 j⟩, ?_⟩
  change R 0 j = 0
  rw [hR.2]
  rfl
end RothschildStein.L1
