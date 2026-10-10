-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactTestIntegrability
public import RothschildStein.S.ClassicalWords

/-! # Compact tests for divergence-free fields

Local integration by parts has no divergence term for divergence-free fields.
Smooth field derivatives of compact tests retain their compact support.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open RothschildStein Hormander.Interface

namespace HeatKernel

/-- A globally smooth field preserves smoothness under one classical differentiation. -/
theorem contDiff_fieldDerivative_of_contDiff {n : ℕ}
    (V : (Fin n → ℝ) → Fin n → ℝ) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative V φ) := by
  exact contDiffOn_univ.mp (S.contDiffOn_fieldDerivative
    (⟨Set.univ, isOpen_univ⟩ : Opens (Fin n → ℝ)) V φ hV.contDiffOn hφ.contDiffOn)

/-- Products of locally integrable functions with compact field derivatives are integrable. -/
theorem integrable_mul_fieldDerivative_compact_test {n : ℕ}
    {Ω : Set (Fin n → ℝ)} {v : (Fin n → ℝ) → ℝ}
    (hv : LocallyIntegrableOn v Ω volume)
    (V : (Fin n → ℝ) → Fin n → ℝ) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => v x * fieldDerivative V φ x) := by
  have hsub := S.tsupport_fieldDerivative_subset V φ
  exact integrable_mul_compact_test_of_locallyIntegrableOn hv
    (contDiff_fieldDerivative_of_contDiff V hV φ hφ).continuous
    (hc.of_isClosed_subset (isClosed_tsupport _) hsub) (hsub.trans hs)

/-- Local integration by parts for a divergence-free field on a compact test. -/
theorem integral_fieldDerivative_mul_compact_test_eq_neg {n : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → Fin n → ℝ)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (hdiv : ∀ x ∈ Ω, euclideanDivergence V x = 0)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in (Ω : Set (Fin n → ℝ)), fieldDerivative V v x * φ x) =
      -(∫ x in (Ω : Set (Fin n → ℝ)), v x * fieldDerivative V φ x) := by
  let ψ : TestFunction Ω ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, hs⟩
  have hi := S.integral_fieldDerivative_mul_test Ω V hV v (hv.of_le (by simp)) ψ
  change (∫ x in (Ω : Set (Fin n → ℝ)), fieldDerivative V v x * φ x) =
    ∫ x in (Ω : Set (Fin n → ℝ)), v x * fieldTranspose V φ x at hi
  rw [hi, ← integral_neg]
  apply setIntegral_congr_fun Ω.isOpen.measurableSet
  intro x hx
  change v x * fieldTranspose V φ x = -(v x * fieldDerivative V φ x)
  rw [S.fieldTranspose_formula V φ x
    ((hV.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp))
    (hφ.differentiable (by simp) x), hdiv x hx]
  ring

end HeatKernel
