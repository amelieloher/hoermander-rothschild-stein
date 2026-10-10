-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScaledEnergyOperators
public import HeatKernel.Form.GroupCutoffCovariance
import Mathlib.Tactic.Linter

/-! # Translation and dilation operators on the horizontal energy Hilbert space -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein RothschildStein.G2

namespace HeatKernel

/-- Horizontal field differentiation intertwines left translation. -/
theorem fieldDerivative_horizontal_comp_leftTranslation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (y : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin q) :
    fieldDerivative (G.horizontalFields hq i) (f ∘ G.mul y) =
      fieldDerivative (G.horizontalFields hq i) f ∘ G.mul y := by
  have H : IsLeftInvariantField G (G.horizontalFields hq i) := by
    simpa only [HomogeneousGroup.horizontalFields, canonicalField_eq_leftField] using
      leftField_invariant G (Hormander.Interface.basisVec (Fin.castLE hq i))
  exact H.operator G f hf y

/-- Weight-one horizontal differentiation intertwines positive dilation with degree one. -/
theorem fieldDerivative_horizontal_comp_dilate {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r : ℝ} (hr : 0 < r) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin q) :
    fieldDerivative (G.horizontalFields hq i) (f ∘ G.dilate r) =
      (fun x => r * fieldDerivative (G.horizontalFields hq i) f (G.dilate r x)) := by
  funext x
  have H := (isHomogeneousField_iff_operator G (G.canonicalField (Fin.castLE hq i))
    (G.weight (Fin.castLE hq i))).mp (canonicalField_homogeneous G (Fin.castLE hq i)) f hf r hr x
  simpa only [HomogeneousGroup.horizontalFields, hw i, Nat.cast_one, Real.rpow_one,
    Function.comp_def] using H

/-- Left translation as a bounded linear operator on the energy Hilbert space. -/
def energyLeftTranslation {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (y : Fin N → ℝ) :
    energyGraph (N := N) ⊤ (G.horizontalFields hq) →L[ℝ]
      energyGraph (N := N) ⊤ (G.horizontalFields hq) :=
  scaledEnergyPullbackLinearMap (G.horizontalFields hq) (leftTranslationHomeomorph G y)
    (contDiff_leftTranslation G y) (J := 1) (by simp)
    (by
      change Measure.map (G.mul y) volume = (1 : ENNReal) • volume
      simpa only [one_smul] using (measurePreserving_leftTranslation G y).map_eq) 1
    (fun f hf i => by
      change fieldDerivative (G.horizontalFields hq i) (f ∘ G.mul y) =
        (fun x => 1 * fieldDerivative (G.horizontalFields hq i) f (G.mul y x))
      simpa only [one_mul, Function.comp_def] using
        fieldDerivative_horizontal_comp_leftTranslation G hq y hf i)

/-- Positive dilation as a bounded linear operator on the energy Hilbert space. -/
def energyDilation {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) {r : ℝ} (hr : 0 < r) :
    energyGraph (N := N) ⊤ (G.horizontalFields hq) →L[ℝ]
      energyGraph (N := N) ⊤ (G.horizontalFields hq) :=
  scaledEnergyPullbackLinearMap (G.horizontalFields hq) (dilationHomeomorph G r hr)
    (contDiff_dilate G r) ENNReal.ofReal_ne_top (map_dilate_volume G hr) r
    (fun _f hf i => fieldDerivative_horizontal_comp_dilate G hq hw hr hf i)

/-- Translation operators preserve the complete bilinear horizontal form. -/
theorem horizontalEnergy_energyLeftTranslation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (y : Fin N → ℝ)
    (u v : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    horizontalEnergy ⊤ (G.horizontalFields hq) (energyLeftTranslation G hq y u)
      (energyLeftTranslation G hq y v) = horizontalEnergy ⊤ (G.horizontalFields hq) u v := by
  simpa only [energyLeftTranslation, one_pow, ENNReal.toReal_one, one_mul] using
    horizontalEnergy_scaledEnergyPullbackLinearMap (G.horizontalFields hq)
      (leftTranslationHomeomorph G y) (contDiff_leftTranslation G y) (J := 1) (by simp)
      (by
      change Measure.map (G.mul y) volume = (1 : ENNReal) • volume
      simpa only [one_smul] using (measurePreserving_leftTranslation G y).map_eq) 1
      (fun f hf i => by
        change fieldDerivative (G.horizontalFields hq i) (f ∘ G.mul y) =
          (fun x => 1 * fieldDerivative (G.horizontalFields hq i) f (G.mul y x))
        simpa only [one_mul, Function.comp_def] using
          fieldDerivative_horizontal_comp_leftTranslation G hq y hf i) u v

/-- Dilation operators have the degree-two minus homogeneous-dimension energy scaling. -/
theorem horizontalEnergy_energyDilation {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {r : ℝ} (hr : 0 < r) (u v : energyGraph (N := N) ⊤ (G.horizontalFields hq)) :
    horizontalEnergy ⊤ (G.horizontalFields hq) (energyDilation G hq hw hr u)
      (energyDilation G hq hw hr v) =
      r ^ (2 - (G.homogeneousDimension : ℝ)) * horizontalEnergy ⊤ (G.horizontalFields hq) u v := by
  have H := horizontalEnergy_scaledEnergyPullbackLinearMap (G.horizontalFields hq)
    (dilationHomeomorph G r hr) (contDiff_dilate G r) ENNReal.ofReal_ne_top
    (map_dilate_volume G hr) r
    (fun _f hf i => fieldDerivative_horizontal_comp_dilate G hq hw hr hf i) u v
  change horizontalEnergy ⊤ (G.horizontalFields hq) (energyDilation G hq hw hr u)
    (energyDilation G hq hw hr v) = _ at H
  rw [H, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hr.le _))]
  have hs : r ^ (2 : ℕ) * (r ^ G.homogeneousDimension)⁻¹ =
      r ^ (2 - (G.homogeneousDimension : ℝ)) := by
    rw [Real.rpow_sub hr]
    simp only [Real.rpow_two, Real.rpow_natCast, div_eq_mul_inv]
  rw [hs]



end HeatKernel
