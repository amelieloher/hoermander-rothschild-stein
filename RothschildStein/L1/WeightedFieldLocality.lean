-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedFieldLinear
public import RothschildStein.L1.WeightedJetLocality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Field classes depend only on the actual coefficients on the open domain. -/
theorem fieldJetClass_congr {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {R S : (Fin N → ℝ) → (Fin N → ℝ)} (hR : fieldJetClass Ω ω a p R)
    (he : EqOn S R Ω) : fieldJetClass Ω ω a p S := by
  refine ⟨hR.1.congr he, ?_⟩
  intro j
  exact (scalarJetClass_congr Ω h0
    (show scalarJetClass Ω ω (a + ω j) p (fun u => R u j) from ⟨contDiffOn_pi.mp hR.1 j, hR.2 j⟩)
    (fun u hu => congrFun (he hu) j)).2

end RothschildStein.L1
