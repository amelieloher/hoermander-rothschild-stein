-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.AffineJetBounds
public import RothschildStein.G3.PrimitiveFiniteJetBCHComparison
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

/-- Coordinate tests translated to the buffer centre have jet bounds
independent of its absolute position. -/
def translatedCoordinateTest {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (x₀ : Fin N → ℝ) (j : Fin N) : smoothOnFunctions Ω :=
  ⟨fun x => -x₀ j + x j, (contDiff_const.add
    (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ).contDiff).contDiffOn⟩

theorem norm_translatedCoordinateTest_jet_le {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (x₀ : Fin N → ℝ) (j : Fin N) {r : ℝ} {x : Fin N → ℝ}
    (hx : x ∈ closedBall x₀ r) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (translatedCoordinateTest Ω x₀ j).val x‖ ≤ max r 1 := by
  let L : (Fin N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  apply G4.norm_affine_jet_le L (-x₀ j) x k
  · have he : ‖x j - x₀ j‖ ≤ r :=
      (norm_le_pi_norm (x-x₀) j).trans (by simpa [dist_eq_norm] using hx)
    simpa only [L, ContinuousLinearMap.proj_apply, neg_add_eq_sub] using he.trans (le_max_left r 1)
  · apply le_trans _ (le_max_right r 1)
    apply L.opNorm_le_bound zero_le_one
    intro y
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm y j
end RothschildStein.G3
