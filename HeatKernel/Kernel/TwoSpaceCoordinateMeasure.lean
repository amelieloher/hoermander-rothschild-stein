-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateRepresentatives

/-! # Associated spacetime coordinates and positive-time measure

Associating the first spatial block with time gives the product measure used to
identify joint representatives from fixed-endpoint spacetime sections.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Separate spacetime into a time-space pair followed by the second spatial block. -/
def timeTwoSpaceCoordinatesAssoc (n : ℕ) :
    (Fin (1 + (n + n)) → ℝ) ≃L[ℝ] (ℝ × (Fin n → ℝ)) × (Fin n → ℝ) :=
  (timeTwoSpaceCoordinates n).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ (Fin n → ℝ) (Fin n → ℝ)).symm

@[simp] theorem timeTwoSpaceCoordinatesAssoc_fst_fst (n : ℕ)
    (z : Fin (1 + (n + n)) → ℝ) : (timeTwoSpaceCoordinatesAssoc n z).1.1 = z 0 := rfl

/-- Associated spacetime coordinates preserve full Lebesgue measure. -/
theorem measurePreserving_timeTwoSpaceCoordinatesAssoc (n : ℕ) :
    MeasurePreserving (timeTwoSpaceCoordinatesAssoc n) := by
  have hp := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : ((ℝ × (Fin n → ℝ)) × (Fin n → ℝ)) ≃ᵐ
      (ℝ × ((Fin n → ℝ) × (Fin n → ℝ))))
    (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := Fin n → ℝ) (γ₁ := Fin n → ℝ))
  exact hp.comp (measurePreserving_timeTwoSpaceCoordinates n)

/-- Associated spacetime coordinates preserve the measure restricted to positive time. -/
theorem measurePreserving_timeTwoSpaceCoordinatesAssoc_positive (n : ℕ) :
    MeasurePreserving (timeTwoSpaceCoordinatesAssoc n)
      (volume.restrict {z : Fin (1 + (n + n)) → ℝ | 0 < z 0})
      ((volume.restrict {p : ℝ × (Fin n → ℝ) | 0 < p.1}).prod volume) := by
  have hpre : timeTwoSpaceCoordinatesAssoc n ⁻¹'
      ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ) = {z | 0 < z 0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      timeTwoSpaceCoordinatesAssoc_fst_fst, Set.mem_ofPred_eq]
  rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
  have h := (measurePreserving_timeTwoSpaceCoordinatesAssoc n).restrict_preimage_emb
    (timeTwoSpaceCoordinatesAssoc n).toHomeomorph.measurableEmbedding
    ({p : ℝ × (Fin n → ℝ) | 0 < p.1} ×ˢ Set.univ)
  rw [hpre] at h
  exact h

/-- Pulling a positive-time coordinate representative back gives product almost-everywhere equality. -/
theorem ae_eq_comp_timeTwoSpaceCoordinatesAssoc_symm {n : ℕ}
    {f g : (Fin (1 + (n + n)) → ℝ) → ℝ}
    (hfg : f =ᵐ[volume.restrict {z | 0 < z 0}] g) :
    (fun p => f ((timeTwoSpaceCoordinatesAssoc n).symm p)) =ᵐ[
      (volume.restrict {p : ℝ × (Fin n → ℝ) | 0 < p.1}).prod volume]
      (fun p => g ((timeTwoSpaceCoordinatesAssoc n).symm p)) :=
  (MeasurePreserving.symm (timeTwoSpaceCoordinatesAssoc n).toHomeomorph.toMeasurableEquiv
    (measurePreserving_timeTwoSpaceCoordinatesAssoc_positive n)).quasiMeasurePreserving.ae_eq_comp hfg

end HeatKernel
