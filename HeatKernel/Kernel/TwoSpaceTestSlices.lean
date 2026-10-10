-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceCoordinateMeasure
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

/-! # Compact test slices in two-space coordinates

Fixing the second spatial endpoint gives a closed affine embedding of ordinary
spacetime. Smooth compact tests restrict to smooth compact positive-time tests.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- Insert a fixed second endpoint into a time-space coordinate vector. -/
def twoSpaceCoordinateSlice {n : ℕ} (y : Fin n → ℝ)
    (z : Fin (1 + n) → ℝ) : Fin (1 + (n + n)) → ℝ :=
  (timeTwoSpaceCoordinatesAssoc n).symm (timeSpaceCoordinates n z, y)

/-- Inserting a fixed spatial endpoint preserves the time coordinate. -/
theorem twoSpaceCoordinateSlice_time {n : ℕ} (y : Fin n → ℝ) (z : Fin (1 + n) → ℝ) :
    twoSpaceCoordinateSlice y z 0 = z 0 := by
  change (timeTwoSpaceCoordinatesAssoc n
    ((timeTwoSpaceCoordinatesAssoc n).symm (timeSpaceCoordinates n z, y))).1.1 = z 0
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Insertion of a fixed endpoint is smooth. -/
theorem contDiff_twoSpaceCoordinateSlice {n : ℕ} (y : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (twoSpaceCoordinateSlice y) :=
  (timeTwoSpaceCoordinatesAssoc n).symm.contDiff.comp
    ((timeSpaceCoordinates n).contDiff.prodMk contDiff_const)

/-- Insertion of a fixed endpoint is a closed embedding. -/
theorem isClosedEmbedding_twoSpaceCoordinateSlice {n : ℕ} (y : Fin n → ℝ) :
    Topology.IsClosedEmbedding (twoSpaceCoordinateSlice y) := by
  have hi : Topology.IsClosedEmbedding
      (fun p : ℝ × (Fin n → ℝ) => (p, y)) := by
    refine ⟨isEmbedding_prodMkLeft y, ?_⟩
    have hr : Set.range (fun p : ℝ × (Fin n → ℝ) => (p, y)) = Set.univ ×ˢ {y} := by
      ext p
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨Set.mem_univ _, rfl⟩
      · intro hp
        exact ⟨p.1, Prod.ext rfl hp.2.symm⟩
    rw [hr]
    exact isClosed_univ.prod isClosed_singleton
  exact (timeTwoSpaceCoordinatesAssoc n).symm.toHomeomorph.isClosedEmbedding.comp
    (hi.comp (timeSpaceCoordinates n).toHomeomorph.isClosedEmbedding)

/-- A smooth compact two-space test restricts to a smooth compact positive-time section test. -/
theorem smooth_compact_positive_twoSpace_test_slice {n : ℕ}
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {z | 0 < z 0}) (y : Fin n → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ ∘ twoSpaceCoordinateSlice y) ∧
      HasCompactSupport (φ ∘ twoSpaceCoordinateSlice y) ∧
      tsupport (φ ∘ twoSpaceCoordinateSlice y) ⊆ {z | 0 < z 0} := by
  refine ⟨hφ.comp (contDiff_twoSpaceCoordinateSlice y),
    hc.comp_isClosedEmbedding (isClosedEmbedding_twoSpaceCoordinateSlice y), ?_⟩
  intro z hz
  have hfull := hs (tsupport_comp_subset_preimage φ (contDiff_twoSpaceCoordinateSlice y).continuous hz)
  simpa only [Set.mem_ofPred_eq, twoSpaceCoordinateSlice_time] using hfull

end HeatKernel
