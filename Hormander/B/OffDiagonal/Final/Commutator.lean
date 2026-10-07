-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Nested.NestedOrder
public import Hormander.B.OffDiagonal.Operators
public import Hormander.B.Mollifier.EFacing
public import Hormander.D.Cutoffs

/-!
# Off-diagonal smoothing by iterated commutators

Route: for `ψ ≺ g ≺ φ` the separated tail satisfies
`(1 - φ) Λ^σ M_ψ = (-1)^k (1 - φ) ad_g^k(Λ^σ) M_ψ`, and the `k`-fold multiplier commutator has
order `σ - k`.
-/

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- The cutoff complement `1 - φ` as an operator. -/
def complementOperator (φ : SchwartzMap (Carrier N) ℝ) : Operator N :=
  LinearMap.id - realMultiplierOperator φ

theorem hasOrder_complementOperator (φ : SchwartzMap (Carrier N) ℝ) :
    HasOrder 0 (complementOperator φ) := by
  have h1 : HasOrder 0 (LinearMap.id : Operator N) := by
    intro s
    exact ⟨1, fun u => by simp⟩
  have h2 : HasOrder 0 ((-1 : ℂ) • realMultiplierOperator φ) :=
    (hasOrder_multiplierOperator_zero (complexifyRealSchwartz φ)).smul _
  have := h1.add h2
  convert this using 1
  ext u x
  simp [complementOperator, sub_eq_add_neg]

theorem multiplier_comp_eq {g ψ : SchwartzMap (Carrier N) ℝ}
    (hg : ∀ x, ψ x ≠ 0 → g x = 1) :
    (realMultiplierOperator g).comp (realMultiplierOperator ψ) = realMultiplierOperator ψ := by
  ext u x
  simp only [realMultiplierOperator, LinearMap.comp_apply, multiplierOperator_apply,
    complexifyRealSchwartz_apply]
  by_cases h : ψ x = 0
  · simp [h]
  · rw [hg x h]; simp

theorem complement_comp_multiplier {g φ : SchwartzMap (Carrier N) ℝ}
    (hg : ∀ x, g x ≠ 0 → φ x = 1) :
    (complementOperator φ).comp (realMultiplierOperator g) = 0 := by
  ext u x
  by_cases h : g x = 0
  · simp [complementOperator, realMultiplierOperator, multiplierOperator_apply,
      complexifyRealSchwartz_apply, h]
  · simp [complementOperator, realMultiplierOperator, multiplierOperator_apply,
      complexifyRealSchwartz_apply, hg x h]

/-- One commutation step: `P B M_ψ = - P [M_g, B] M_ψ`. -/
theorem complement_step {g ψ φ : SchwartzMap (Carrier N) ℝ}
    (hψ : ∀ x, ψ x ≠ 0 → g x = 1) (hφ : ∀ x, g x ≠ 0 → φ x = 1) (B : Operator N) :
    (complementOperator φ).comp (B.comp (realMultiplierOperator ψ)) =
      -((complementOperator φ).comp
        ((operatorComm (realMultiplierOperator g) B).comp (realMultiplierOperator ψ))) := by
  have e1 := multiplier_comp_eq hψ
  have e2 := complement_comp_multiplier hφ
  have : (complementOperator φ).comp
      ((operatorComm (realMultiplierOperator g) B).comp (realMultiplierOperator ψ)) =
      ((complementOperator φ).comp (realMultiplierOperator g)).comp
        (B.comp (realMultiplierOperator ψ)) -
      (complementOperator φ).comp (B.comp ((realMultiplierOperator g).comp
        (realMultiplierOperator ψ))) := by
    simp only [operatorComm, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.comp_assoc]
  rw [this, e1, e2]
  simp

theorem tail_eq_iterated {g ψ φ : SchwartzMap (Carrier N) ℝ}
    (hψ : ∀ x, ψ x ≠ 0 → g x = 1) (hφ : ∀ x, g x ≠ 0 → φ x = 1) (σ : ℝ) :
    ∀ k : ℕ, (complementOperator φ).comp ((lambdaOperator σ).comp (realMultiplierOperator ψ)) =
      ((-1 : ℂ) ^ k) • (complementOperator φ).comp
        ((iteratedCommutator ((List.replicate k g).map OperatorGenerator.multiplier)
          (lambdaOperator σ)).comp (realMultiplierOperator ψ)) := by
  intro k
  induction k with
  | zero => simp [iteratedCommutator]
  | succ k ih =>
    rw [ih, List.replicate_succ, List.map_cons, iteratedCommutator,
      complement_step hψ hφ]
    ext u x
    simp [pow_succ, OperatorGenerator.toOperator]

/-- Analytic form of the off-diagonal smoothing estimate. -/
theorem offDiagonalTail_order_of_sandwich {g ψ φ : SchwartzMap (Carrier N) ℝ}
    (hψ : ∀ x, ψ x ≠ 0 → g x = 1) (hφ : ∀ x, g x ≠ 0 → φ x = 1) (σ τ : ℝ) :
    HasOrder (-τ) (offDiagonalTailOperator φ ψ σ) := by
  set k := ⌈σ + τ⌉₊
  have hk : σ + τ ≤ k := Nat.le_ceil _
  have h0 := nested_multiplier_order σ (List.replicate k g)
  rw [List.length_replicate] at h0
  have h1 := (hasOrder_complementOperator φ).comp
    (h0.comp (hasOrder_multiplierOperator_zero (complexifyRealSchwartz ψ)))
  have h2 := (h1.smul ((-1 : ℂ) ^ k)).mono (m' := -τ) (by linarith)
  have heq : offDiagonalTailOperator φ ψ σ =
      ((-1 : ℂ) ^ k) • (complementOperator φ).comp
        ((iteratedCommutator ((List.replicate k g).map OperatorGenerator.multiplier)
          (lambdaOperator σ)).comp (realMultiplierOperator ψ)) :=
    tail_eq_iterated hψ hφ σ k
  rw [heq]
  exact h2

end Hormander.B
