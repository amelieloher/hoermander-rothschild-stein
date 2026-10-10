-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.HorizontalPullbackOperators
public import HeatKernel.Form.EnergyRepresentatives
import Mathlib.Tactic.Linter

/-! # Composition and inverse identities for energy translations and dilations -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein RothschildStein.G2

namespace HeatKernel

variable {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)

/-- Canonical horizontal fields are smooth without requiring a separate regularity premise. -/
theorem contDiff_horizontalFields (i : Fin q) :
    ContDiff ℝ (⊤ : ℕ∞) (G.horizontalFields hq i) := by
  simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
    contDiff_leftField G (Hormander.Interface.basisVec (Fin.castLE hq i))

/-- The translation operator has composition by left multiplication as scalar representative. -/
theorem energyLeftTranslation_ae (y : Fin N → ℝ)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyInclusion ⊤ (G.horizontalFields hq) (energyLeftTranslation G hq y u) =ᵐ[volume]
      (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ G.mul y := by
  unfold energyLeftTranslation
  change _ =ᵐ[volume] (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ (leftTranslationHomeomorph G y)
  exact energyInclusion_scaledEnergyPullbackLinearMap_ae _ _ _ _ _ _ _ u

/-- The dilation operator has composition by dilation as scalar representative. -/
theorem energyDilation_ae (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r : ℝ} (hr : 0 < r) (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyInclusion ⊤ (G.horizontalFields hq) (energyDilation G hq hw hr u) =ᵐ[volume]
      (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ G.dilate r := by
  unfold energyDilation
  change _ =ᵐ[volume] (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ (dilationHomeomorph G r hr)
  exact energyInclusion_scaledEnergyPullbackLinearMap_ae _ _ _ _ _ _ _ u

/-- Translation by the group identity acts as the identity on the energy domain. -/
theorem energyLeftTranslation_zero (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyLeftTranslation G hq 0 u = u := by
  apply energyGraph_ext_of_ae ⊤ (G.horizontalFields hq) (fun i => (contDiff_horizontalFields G hq i).contDiffOn)
  simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def, zero_mul G] using
    energyLeftTranslation_ae G hq 0 u

/-- Composition of scalar pullbacks reverses the order of the group multipliers. -/
theorem energyLeftTranslation_comp (y z : Fin N → ℝ)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyLeftTranslation G hq y (energyLeftTranslation G hq z u) =
      energyLeftTranslation G hq (G.mul z y) u := by
  apply energyGraph_ext_of_ae ⊤ (G.horizontalFields hq) (fun i => (contDiff_horizontalFields G hq i).contDiffOn)
  have H := (energyLeftTranslation_ae G hq y (energyLeftTranslation G hq z u)).trans
    ((measurePreserving_leftTranslation G y).quasiMeasurePreserving.ae_eq_comp (energyLeftTranslation_ae G hq z u))
  have H' : energyInclusion ⊤ (G.horizontalFields hq) (energyLeftTranslation G hq y (energyLeftTranslation G hq z u))
      =ᵐ[volume] (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ G.mul (G.mul z y) := by
    simpa only [Function.comp_def, mul_assoc G] using H
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    H'.trans (energyLeftTranslation_ae G hq (G.mul z y) u).symm

/-- The inverse group translation is an inverse energy operator. -/
theorem energyLeftTranslation_inv (y : Fin N → ℝ)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyLeftTranslation G hq (G.inv y) (energyLeftTranslation G hq y u) = u := by
  rw [energyLeftTranslation_comp, mul_inv G, energyLeftTranslation_zero]

/-- Unit dilation acts as the identity on the energy domain. -/
theorem energyDilation_one (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyDilation G hq hw zero_lt_one u = u := by
  apply energyGraph_ext_of_ae ⊤ (G.horizontalFields hq) (fun i => (contDiff_horizontalFields G hq i).contDiffOn)
  simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def, dilate_one G] using
    energyDilation_ae G hq hw zero_lt_one u

/-- Positive dilation operators compose multiplicatively. -/
theorem energyDilation_comp (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyDilation G hq hw hr (energyDilation G hq hw hs u) = energyDilation G hq hw (mul_pos hs hr) u := by
  apply energyGraph_ext_of_ae ⊤ (G.horizontalFields hq) (fun i => (contDiff_horizontalFields G hq i).contDiffOn)
  have hqm : Measure.QuasiMeasurePreserving (G.dilate r) volume volume :=
    ⟨(contDiff_dilate G r).continuous.measurable, by
      rw [map_dilate_volume G hr]
      exact Measure.smul_absolutelyContinuous⟩
  have H := (energyDilation_ae G hq hw hr (energyDilation G hq hw hs u)).trans
    (hqm.ae_eq_comp (energyDilation_ae G hq hw hs u))
  have H' : energyInclusion ⊤ (G.horizontalFields hq) (energyDilation G hq hw hr (energyDilation G hq hw hs u))
      =ᵐ[volume] (energyInclusion ⊤ (G.horizontalFields hq) u) ∘ G.dilate (s * r) := by
    simpa only [Function.comp_def, dilate_dilate G] using H
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    H'.trans (energyDilation_ae G hq hw (mul_pos hs hr) u).symm

/-- Reciprocal dilation is an inverse energy operator. -/
theorem energyDilation_inv (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r : ℝ} (hr : 0 < r) (u : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    energyDilation G hq hw (inv_pos.mpr hr) (energyDilation G hq hw hr u) = u := by
  rw [energyDilation_comp]
  simpa only [mul_inv_cancel₀ hr.ne'] using energyDilation_one G hq hw u



end HeatKernel
