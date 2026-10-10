-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Weak horizontal derivatives of smooth spatial slices

Joint smoothness on a cylinder gives smooth spatial slices. Their classical
horizontal derivatives represent the corresponding weak word derivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open RothschildStein

namespace HeatKernel

/-- Joint smoothness on a product domain restricts to every spatial slice. -/
theorem contDiffOn_spatial_slice {n : ℕ} {I : Set ℝ} {U : Set (Fin n → ℝ)}
    {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2)
      (I ×ˢ U)) {t : ℝ} (ht : t ∈ I) :
    ContDiffOn ℝ (⊤ : ℕ∞) (u t) U := by
  exact hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ⟨ht, hx⟩)

/-- The classical horizontal derivative of a smooth spatial slice is its weak derivative. -/
theorem hasWeakWordDeriv_classical_spatial_slice {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (U : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    {I : Set ℝ} {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2)
      (I ×ˢ (U : Set (Fin n → ℝ)))) {t : ℝ} (ht : t ∈ I) (i : Fin q) :
    hasWeakWordDeriv X U [i] (u t) (fieldDerivative (X i) (u t)) := by
  simpa only [wordDerivative] using
    S.hasWeakWordDeriv_classical U X hX [i] (u t) (contDiffOn_spatial_slice hu ht)

/-- Jointly smooth functions have their classical horizontal weak gradients at almost every time. -/
theorem ae_hasWeakWordDeriv_classical_spatial_slice {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (I : Opens ℝ) (U : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin n → ℝ)))
    {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin n → ℝ) => u z.1 z.2)
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ)))) :
    ∀ᵐ t ∂volume.restrict (I : Set ℝ), ∀ i,
      hasWeakWordDeriv X U [i] (u t) (fieldDerivative (X i) (u t)) := by
  filter_upwards [ae_restrict_mem I.isOpen.measurableSet] with t ht
  exact fun i => hasWeakWordDeriv_classical_spatial_slice X U hX hu ht i

end HeatKernel
