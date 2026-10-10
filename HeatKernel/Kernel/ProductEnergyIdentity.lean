-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateEnergyIdentity
public import HeatKernel.Kernel.CoordinateProductDerivatives
public import HeatKernel.Kernel.CoordinateMeasure

/-! # Energy test identities in product spacetime

The measure-preserving time-space equivalence transports the coordinate energy
identity to product spacetime. Compact support keeps every test inside positive time.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open RothschildStein

namespace HeatKernel

/-- Coordinate heat solutions satisfy the product-spacetime first-order energy identity. -/
theorem integral_product_heat_energy_test_eq_zero {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n)
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ z, 0 < z 0 →
      fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v) z)
    (φ : ℝ × (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {p | 0 < p.1}) :
    Integrable (fun p : ℝ × (Fin n → ℝ) =>
      -(v ((timeSpaceCoordinates n).symm p) * fderiv ℝ φ p (1, 0)) +
        ∑ i : Fin q, fieldDerivative (G.horizontalFields hq i)
          (fun y => v ((timeSpaceCoordinates n).symm (p.1, y))) p.2 *
          fderiv ℝ φ p (0, G.horizontalFields hq i p.2)) ∧
    (∫ p : ℝ × (Fin n → ℝ),
      -(v ((timeSpaceCoordinates n).symm p) * fderiv ℝ φ p (1, 0)) +
        ∑ i : Fin q, fieldDerivative (G.horizontalFields hq i)
          (fun y => v ((timeSpaceCoordinates n).symm (p.1, y))) p.2 *
          fderiv ℝ φ p (0, G.horizontalFields hq i p.2)) = 0 := by
  let ψ := φ ∘ timeSpaceCoordinates n
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (timeSpaceCoordinates n).contDiff
  have hcψ : HasCompactSupport ψ :=
    hc.comp_isClosedEmbedding (timeSpaceCoordinates n).toHomeomorph.isClosedEmbedding
  have hsψ : tsupport ψ ⊆ {z | 0 < z 0} := by
    intro z hz
    exact hs (tsupport_comp_subset_preimage φ (timeSpaceCoordinates n).continuous hz)
  have hcoord := integral_coordinate_heat_energy_test_eq_zero G hq v hv hheat ψ hψ hcψ hsψ
  let F : ℝ × (Fin n → ℝ) → ℝ := fun p =>
    -(v ((timeSpaceCoordinates n).symm p) * fderiv ℝ φ p (1, 0)) +
      ∑ i : Fin q, fieldDerivative (G.horizontalFields hq i)
        (fun y => v ((timeSpaceCoordinates n).symm (p.1, y))) p.2 *
        fderiv ℝ φ p (0, G.horizontalFields hq i p.2)
  let H : (Fin (1 + n) → ℝ) → ℝ := fun z =>
    -(v z * fderiv ℝ ψ z (leftCoordinateInclusion 1 n (fun _ => 1))) +
      ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) v z *
        fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) ψ z
  have ht (z : Fin (1 + n) → ℝ) :
      fderiv ℝ ψ z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        fderiv ℝ φ (timeSpaceCoordinates n z) (1, 0) :=
    fderiv_time_comp_timeSpaceCoordinates φ z (hφ.differentiable (by simp) _)
  have hi (i : Fin q) (z : Fin (1 + n) → ℝ) :
      fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) ψ z =
        fderiv ℝ φ (timeSpaceCoordinates n z)
          (0, G.horizontalFields hq i (timeSpaceCoordinates n z).2) :=
    fieldDerivative_comp_timeSpaceCoordinates _ φ z (hφ.differentiable (by simp) _)
  have hcomp (z : Fin (1 + n) → ℝ) : F (timeSpaceCoordinates n z) = H z := by
    dsimp only [F, H]
    rw [ContinuousLinearEquiv.symm_apply_apply, ht]
    simp_rw [hi]
    by_cases hz : 0 < z 0
    · have hd : DifferentiableAt ℝ v
          ((timeSpaceCoordinates n).symm ((timeSpaceCoordinates n z).1, (timeSpaceCoordinates n z).2)) := by
        simpa only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
          (hv.contDiffAt ((isOpen_positive_time n).mem_nhds hz)).differentiableAt (by simp)
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldDerivative_spatial_coordinate_slice _ v _ _ hd]
      simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply]
    · have hnot : timeSpaceCoordinates n z ∉ tsupport φ := fun h => hz (hs h)
      have hd := fderiv_of_notMem_tsupport ℝ hnot
      simp only [hd, zero_apply, mul_zero, Finset.sum_const_zero,
        neg_zero, add_zero]
  have heq : F ∘ timeSpaceCoordinates n = H := funext hcomp
  have hInt : Integrable (F ∘ timeSpaceCoordinates n) := by
    rw [heq]
    exact hcoord.1
  refine ⟨((measurePreserving_timeSpaceCoordinates n).integrable_comp_emb
    (timeSpaceCoordinates n).toHomeomorph.measurableEmbedding).mp hInt, ?_⟩
  change (∫ p, F p) = 0
  rw [← integral_timeSpaceCoordinates n F]
  simpa only [hcomp] using hcoord.2

end HeatKernel
