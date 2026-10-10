-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ProductEnergyIdentity
public import HeatKernel.Kernel.SmoothCylinderEnergy
public import HeatKernel.Definitions.IsLocalWeakSolution

/-! # Smooth heat solutions as local weak solutions

The coordinate heat equation supplies the literal product test identity.
Smooth spatial slices and compact-cylinder bounds provide the horizontal weak
gradient and every local energy condition of the local weak-solution predicate.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators
open RothschildStein

namespace HeatKernel

/-- A smooth positive-time coordinate heat solution is a local weak solution on each contained cylinder. -/
theorem isLocalWeakSolution_of_coordinate_heat_equation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (I : Opens ℝ) (U : Opens (Fin n → ℝ))
    (hI : ∀ t ∈ I, 0 < t)
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ z, 0 < z 0 →
      fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v) z) :
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun _ _ i j => if i = j then 1 else 0) I U
      (fun t x => v ((timeSpaceCoordinates n).symm (t, x))) := by
  let u : ℝ → (Fin n → ℝ) → ℝ :=
    fun t x => v ((timeSpaceCoordinates n).symm (t, x))
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      ((I : Set ℝ) ×ˢ (U : Set (Fin n → ℝ))) := by
    apply hv.comp (timeSpaceCoordinates n).symm.contDiff.contDiffOn
    intro p hp
    change 0 < (timeSpaceCoordinates n).symm (p.1, p.2) 0
    rw [timeSpaceCoordinates_symm_time]
    exact hI p.1 hp.1
  change IsLocalWeakSolution G hq hqpos hw hspan _ I U u
  refine ⟨hsmooth.continuousOn.aestronglyMeasurable (I.isOpen.prod U.isOpen).measurableSet,
    (fun i t x => fieldDerivative (G.horizontalFields hq i) (u t) x), ?_, ?_, ?_⟩
  · exact ae_hasWeakWordDeriv_classical_spatial_slice (G.horizontalFields hq) I U
      (fun i => (G.horizontalFields_contDiff hq i).contDiffOn) hsmooth
  · intro J K hJ hJI hK hKU
    exact local_energy_bounds_of_contDiffOn (G.horizontalFields hq)
      (G.horizontalFields_contDiff hq) I U hsmooth hJ hJI hK hKU
  · intro φ hφ hc hs
    have hspos : tsupport φ ⊆ {p : ℝ × (Fin n → ℝ) | 0 < p.1} :=
      fun p hp => hI p.1 (hs hp).1
    have htest := integral_product_heat_energy_test_eq_zero G hq v hv hheat φ hφ hc hspos
    simpa only [u, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] using htest

end HeatKernel
