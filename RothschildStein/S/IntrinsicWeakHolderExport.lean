-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicWeakDerivative
public import RothschildStein.S.IntrinsicWeakHolderConditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n q : ℕ}

/-- Every intrinsic Hölder input has weak representatives for the same weighted word family (BB pp. 81, 87–90). -/
theorem memWeakHolderX_of_memHolderX
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X G.d U k α f) : memWeakHolderX w X G.d U k α f :=
  memWeakHolderX_of_intrinsicToWeak hasWeakWordDeriv_of_intrinsic_derivative Ω U G hU w X hX k hα hf

/-- The intrinsic Hölder norm equals the weak norm for every input (BB pp. 81, 87–90). -/
theorem holderXENorm_eq_weakHolderXENorm_of_memHolderX
    (Ω U : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X G.d U k α f) :
    holderXENorm w X G.d U k α f = weakHolderXENorm w X G.d U k α f :=
  holderXENorm_eq_weak_of_intrinsicToWeak hasWeakWordDeriv_of_intrinsic_derivative Ω U G hU w X hX k hα hf

end RothschildStein.S
