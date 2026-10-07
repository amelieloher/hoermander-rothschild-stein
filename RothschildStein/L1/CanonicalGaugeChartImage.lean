-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalAuxiliaryControlCost
public import RothschildStein.G4.WeightedCoefficientBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- A model-weighted coefficient box has canonical gauge at most its
radius; this is the exact coefficient estimate needed for ball-box images. -/
theorem canonical_gauge_le_of_weightedBox {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p) {u : Fin (freeDimension a s p) → ℝ}
    {r : ℝ} (hr : 0 < r) (hu : u ∈ G4.weightedBox (canonicalControlWeight D) r) :
    rsGauge D.group.weight D.group.weight_pos u ≤ r := by
  apply (G2.gauge_le_iff D.group u r).mpr
  intro i
  apply (Real.rpow_inv_le_iff_of_pos (abs_nonneg (u i)) hr.le
    (Nat.cast_pos.mpr (D.group.weight_pos i))).mpr
  simpa only [Real.rpow_natCast,canonicalControlWeight,PNat.mk_coe] using (hu i).le

/-- Once actual trajectories identify the chart maps, image membership
supplies a canonical-gauge bound through the fixed inverse identity. -/
theorem canonical_gauge_le_of_chart_image {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p)
    {Ω : Set (Fin (freeDimension a s p) → ℝ)}
    {X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ)}
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    {η ξ : Fin (freeDimension a s p) → ℝ} (hη : η ∈ ball x C.radius)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hrC : r ≤ C.radius)
    (F : (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hF : EqOn F (fun u => canonicalFrameMap C.time C.flow (η,u))
      (G4.weightedBox (canonicalControlWeight D) r))
    (hξ : ξ ∈ F '' G4.weightedBox (canonicalControlWeight D) r) :
    rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) ≤ r := by
  obtain ⟨u,hu,rfl⟩ := hξ
  have huC : u ∈ ball 0 C.radius := ball_subset_ball hrC
    (G4.weightedBox_subset_ball (canonicalControlWeight D) hr hr1 hu)
  rw [hF hu,(C.coefficients (η,u) ⟨hη,huC⟩).2.2]
  exact canonical_gauge_le_of_weightedBox D hr hu
end RothschildStein.L1
