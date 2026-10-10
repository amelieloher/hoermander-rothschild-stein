-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ClassicalEnergyIdentity
public import HeatKernel.Kernel.ClassicalWeakHeatEquation

/-! # First-order energy tests in heat coordinates

The lifted horizontal fields and the unit time field are divergence-free.
Their classical heat equation therefore gives the first-order energy test identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators
open RothschildStein Hormander.Interface

namespace HeatKernel

/-- A smooth coordinate heat solution has integrable compact first-order energy tests of zero integral. -/
theorem integral_coordinate_heat_energy_test_eq_zero {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ z, 0 < z 0 →
      fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v) z)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {z | 0 < z 0}) :
    Integrable (fun z =>
      -(v z * fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1))) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v z *
          fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) φ z) ∧
    (∫ z, -(v z * fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1))) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v z *
          fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) φ z) = 0 := by
  let Ω : Opens (Fin (1 + n) → ℝ) := ⟨{z | 0 < z 0}, isOpen_positive_time n⟩
  let X := timeSpaceFields 1 (G.horizontalFields hq)
  have hX := contDiff_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq)
  have hdiv : ∀ i z, euclideanDivergence (X i) z = 0 := by
    apply euclideanDivergence_timeSpaceFields 1 _ (G.horizontalFields_contDiff hq)
    intro j z
    simpa only [HomogeneousGroup.horizontalFields, RothschildStein.G2.canonicalField_eq_leftField]
      using RothschildStein.G2.leftField_divergence_zero G (basisVec (Fin.castLE hq j)) z
  have heq : ∀ z ∈ Ω, fieldDerivative (X 0) v z =
      ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) v) z := by
    intro z hz
    simpa only [X, timeSpaceFields_zero, timeSpaceFields_succ, fieldDerivative] using hheat z hz
  simpa only [X, timeSpaceFields_zero, timeSpaceFields_succ, fieldDerivative] using
    integral_classical_energy_test_eq_zero Ω X hX hdiv v hv heq φ hφ hc hs

end HeatKernel
