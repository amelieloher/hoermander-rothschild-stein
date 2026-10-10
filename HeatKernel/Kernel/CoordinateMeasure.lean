-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.Coordinates
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Lebesgue measure in spacetime coordinates

The coordinate splits preserve product Lebesgue measure. Their integral and local integrability
identities allow weak equations to be written in either coordinate system.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open MeasureTheory Set

/-- Splitting consecutive coordinate blocks preserves Lebesgue measure. -/
theorem measurePreserving_splitCoordinates (m n : ℕ) :
    MeasurePreserving (splitCoordinates m n) :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (m + n) => ℝ)
      finSumFinEquiv).symm

/-- Separating time and space preserves product Lebesgue measure. -/
theorem measurePreserving_timeSpaceCoordinates (n : ℕ) :
    MeasurePreserving (timeSpaceCoordinates n) := by
  have hp := (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).prod
    (MeasurePreserving.id (volume : Measure (Fin n → ℝ)))
  have hs := measurePreserving_splitCoordinates 1 n
  simp only [← Measure.volume_eq_prod] at hp
  exact hp.comp hs

/-- Separating time and two spatial blocks preserves product Lebesgue measure. -/
theorem measurePreserving_timeTwoSpaceCoordinates (n : ℕ) :
    MeasurePreserving (timeTwoSpaceCoordinates n) := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_splitCoordinates n n)
  simp only [← Measure.volume_eq_prod] at hp
  exact hp.comp (measurePreserving_timeSpaceCoordinates (n + n))

/-- Change of variables for the time-space coordinate equivalence. -/
theorem integral_timeSpaceCoordinates (n : ℕ) (f : ℝ × (Fin n → ℝ) → ℝ) :
    (∫ x, f (timeSpaceCoordinates n x)) = ∫ x, f x :=
  (measurePreserving_timeSpaceCoordinates n).integral_comp
    (timeSpaceCoordinates n).toHomeomorph.measurableEmbedding f

/-- A measure-preserving homeomorphism transports local integrability on an open set. -/
theorem locallyIntegrableOn_comp_homeomorph
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [LocallyCompactSpace E]
    [MeasureSpace E] [MeasureSpace F] [BorelSpace E] [BorelSpace F]
    (e : E ≃ₜ F) (he : MeasurePreserving e) {s : Set F} (hs : IsOpen s)
    {f : F → ℝ} (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn (f ∘ e) (e ⁻¹' s) volume := by
  rw [locallyIntegrableOn_iff (hs.preimage e.continuous).isLocallyClosed]
  intro K hKs hK
  have hKs' : e '' K ⊆ s := image_subset_iff.mpr hKs
  exact (he.integrableOn_image e.measurableEmbedding).mp
    (hf.integrableOn_compact_subset hKs' (hK.image e.continuous))

/-- Transport local integrability from time-space coordinates to a coordinate vector. -/
theorem locallyIntegrableOn_comp_timeSpaceCoordinates (n : ℕ)
    {s : Set (ℝ × (Fin n → ℝ))} (hs : IsOpen s) {f : ℝ × (Fin n → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn (f ∘ timeSpaceCoordinates n)
      (timeSpaceCoordinates n ⁻¹' s) volume :=
  locallyIntegrableOn_comp_homeomorph (timeSpaceCoordinates n).toHomeomorph
    (measurePreserving_timeSpaceCoordinates n) hs hf

/-- Transport local integrability from time and two-space coordinates to a coordinate vector. -/
theorem locallyIntegrableOn_comp_timeTwoSpaceCoordinates (n : ℕ)
    {s : Set (ℝ × ((Fin n → ℝ) × (Fin n → ℝ)))} (hs : IsOpen s)
    {f : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ}
    (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn (f ∘ timeTwoSpaceCoordinates n)
      (timeTwoSpaceCoordinates n ⁻¹' s) volume :=
  locallyIntegrableOn_comp_homeomorph (timeTwoSpaceCoordinates n).toHomeomorph
    (measurePreserving_timeTwoSpaceCoordinates n) hs hf

end HeatKernel
