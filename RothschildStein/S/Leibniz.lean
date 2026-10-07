-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntegrationByParts
public import RothschildStein.Definitions.wordDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Multiplication by a smooth function obeys the weak first-order product
rule (BB p. 73). -/
theorem hasWeakWordDeriv_mul_one
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (i : Fin m) (f g a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (h : hasWeakWordDeriv X Ω [i] f g) :
    hasWeakWordDeriv X Ω [i] (fun x => f x * a x)
      (fun x => g x * a x + f x * fieldDerivative (X i) a x) := by
  have hd : ContinuousOn (fieldDerivative (X i) a) (Ω : Set (Fin n → ℝ)) :=
    (contDiffOn_fieldDerivative Ω (X i) a (hX i) ha).continuousOn
  have hl₁ := h.2.1.mul_continuousOn ha.continuousOn Ω.isOpen.isLocallyClosed
  have hl₂ := h.1.mul_continuousOn hd Ω.isOpen.isLocallyClosed
  refine ⟨h.1.mul_continuousOn ha.continuousOn Ω.isOpen.isLocallyClosed,
    hl₁.add hl₂, fun ψ => ?_⟩
  let aψ := testMultiplierOn Ω a ha ψ
  have hi := h.2.2 aψ
  have he : ∀ x ∈ (Ω : Set (Fin n → ℝ)),
      fieldTranspose (X i) aψ x =
        a x * fieldTranspose (X i) ψ x - ψ x * fieldDerivative (X i) a x := by
    intro x hx
    have hf : (aψ : (Fin n → ℝ) → ℝ) = fun y => a y * ψ y := by
      funext y
      exact mul_comm _ _
    rw [hf]
    exact fieldTranspose_mul (X i) a ψ x
      ((hX i).contDiffAt (Ω.isOpen.mem_nhds hx) |>.differentiableAt (by simp))
      (ha.contDiffAt (Ω.isOpen.mem_nhds hx) |>.differentiableAt (by simp))
      (ψ.contDiff.differentiable (by simp) |>.differentiableAt)
  have hj : (∫ x in (Ω : Set (Fin n → ℝ)), g x * a x * ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)),
        f x * a x * fieldTranspose (X i) ψ x -
          f x * fieldDerivative (X i) a x * ψ x := by
    calc
      _ = ∫ x in (Ω : Set (Fin n → ℝ)), g x * aψ x := by
        apply integral_congr_ae
        filter_upwards [] with x
        change g x * a x * ψ x = g x * (ψ x * a x)
        ring
      _ = ∫ x in (Ω : Set (Fin n → ℝ)), f x * fieldTranspose (X i) aψ x := hi
      _ = _ := by
        apply setIntegral_congr_fun Ω.isOpen.measurableSet
        intro x hx
        dsimp only
        rw [he x hx]
        ring
  have hleft₁ := (integrable_mul_test Ω hl₁ ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hleft₂ := (integrable_mul_test Ω hl₂ ψ).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  have hright := (integrable_mul_test Ω
    (h.1.mul_continuousOn ha.continuousOn Ω.isOpen.isLocallyClosed)
    (fieldTransposeTest Ω (X i) (hX i) ψ)).integrableOn (s := (Ω : Set (Fin n → ℝ)))
  simp_rw [fieldTransposeTest_apply] at hright
  rw [integral_sub hright hleft₂] at hj
  simp only [wordTranspose]
  simp_rw [add_mul]
  rw [integral_add hleft₁ hleft₂, hj]
  ring

/-- A repeated field contributes the coefficient 2 in the weak square product rule (BB (8.62), p. 375; p. 590). -/
theorem hasWeakWordDeriv_mul_square
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (i : Fin m) (f g h a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (h₁ : hasWeakWordDeriv X Ω [i] f g) (h₂ : hasWeakWordDeriv X Ω [i, i] f h) :
    hasWeakWordDeriv X Ω [i, i] (fun x => f x * a x)
      (fun x => h x * a x + 2 * g x * fieldDerivative (X i) a x +
        f x * fieldDerivative (X i) (fieldDerivative (X i) a) x) := by
  have htail := hasWeakWordDeriv_mul_one X Ω hX i f g a ha h₁
  apply (hasWeakWordDeriv_cons_iff X Ω hX htail i).mpr
  have hh := (hasWeakWordDeriv_cons_iff X Ω hX h₁ i).mp h₂
  have hfirst := hasWeakWordDeriv_mul_one X Ω hX i g h a ha hh
  have hsecond := hasWeakWordDeriv_mul_one X Ω hX i f g (fieldDerivative (X i) a)
    (contDiffOn_fieldDerivative Ω (X i) a (hX i) ha) h₁
  have hsum := hasWeakWordDeriv_add X Ω hX hfirst hsecond
  convert hsum using 1
  funext x
  ring

end RothschildStein.S
