-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftDefs
public import RothschildStein.P1.PaddingDomainSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- Local smoothness of the actual no-drift padded family on
any open product domain projecting into the original coefficient domain. -/
theorem contDiffOn_paddingNoDriftVectorFields_projection {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (U : Set (Fin (n + d) → ℝ))
    (hU : U ⊆ basePoint ⁻¹' Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (paddingNoDriftVectorFields (d := d) X i) U := by
  rw [paddingNoDriftVectorFields_eq_zeroDrift_tail]
  intro i
  exact contDiffOn_paddingVectorFields_projection Ω U hU (P2.zeroDrift X)
    (P2.zeroDrift_contDiffOn hX) i.succ

/-- Adding a temporary zero drift commutes with diffusion
padding. The equation adapter is separate from the free no-drift model. -/
theorem paddingVectorFields_zeroDrift_eq {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingVectorFields (d := d) (P2.zeroDrift X) =
      P2.zeroDrift (paddingNoDriftVectorFields (d := d) X) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · ext ξ j
    simp [paddingVectorFields_zero, P2.zeroDrift, paddingBaseField, joinPoint]
    exact Fin.addCases (fun _ => by simp) (fun _ => by simp) j
  · intro j
    simpa only [P2.zeroDrift, Fin.cons_succ] using
      (congrFun (paddingNoDriftVectorFields_eq_zeroDrift_tail (d := d) X) j).symm

end RothschildStein.P1
