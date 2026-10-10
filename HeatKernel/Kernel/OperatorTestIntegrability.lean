-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactTestIntegrability
public import RothschildStein.P2.ProductAbsorptionCutoffs
public import RothschildStein.S.Transposes

/-! # Integrability of compact differential tests

A smooth differential operator preserves compact test support. Its product
with a locally integrable function is therefore globally integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein

/-- Smooth fields preserve global smoothness under the sum of squares with drift. -/
theorem contDiff_sumSquaresWithDrift_of_contDiff {n q : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift X φ) := by
  have hd (i : Fin (q + 1)) (f : (Fin n → ℝ) → ℝ)
      (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) f) :=
    contDiffOn_univ.mp (S.contDiffOn_fieldDerivative
      (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (Fin n → ℝ))
      (X i) f (hX i).contDiffOn hf.contDiffOn)
  exact (hd 0 φ hφ).add (ContDiff.sum fun i _ => hd i.succ _ (hd i.succ φ hφ))

/-- A locally integrable function times a smooth compact differential test is integrable. -/
theorem integrable_mul_sumSquaresWithDrift_compact_test {n q : ℕ}
    {Ω : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f Ω volume)
    (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun z => f z * sumSquaresWithDrift X φ z) volume := by
  have hsub := P2.tsupport_sumSquaresWithDrift_subset X φ
  exact integrable_mul_compact_test_of_locallyIntegrableOn hf
    (contDiff_sumSquaresWithDrift_of_contDiff X hX φ hφ).continuous
    (hc.of_isClosed_subset (isClosed_tsupport _) hsub) (hsub.trans hs)

end HeatKernel
