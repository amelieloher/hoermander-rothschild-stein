-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1

/-- No nonnegative coordinate weight can lie below a nonpositive threshold. -/
theorem scalarJetVanishing_of_nonpos {N p : ℕ} (ω : Fin N → ℕ) {a : ℝ}
    (ha : a ≤ 0) (f : (Fin N → ℝ) → ℝ) : scalarJetVanishing ω a p f := by
  intro J _ hw
  have hn : (0 : ℝ) ≤ (((J.map ω).sum : ℕ) : ℝ) := Nat.cast_nonneg _
  exfalso
  linarith

/-- The high-weight case is automatic from nonpositive coefficient
thresholds. It imposes no vanishing of the field's value at zero. -/
theorem fullFieldJetClass_of_nonpos_thresholds {N : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (a : ℝ) (R : (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) (ha : ∀ j, a + ω j ≤ 0) :
    fullFieldJetClass Ω ω a R := by
  intro p
  exact ⟨hR, fun j => scalarJetVanishing_of_nonpos ω (ha j) (fun u => R u j)⟩

end RothschildStein.L1
