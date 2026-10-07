-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalAuxiliaryControlCost
public import RothschildStein.L1.CanonicalGaugeSmallPatch
public import RothschildStein.G4.SmoothOrdinaryAuxiliaryMetricComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- The actual canonical gauge bounds ordinary control cost on
a smaller spatial patch. The G1 comparison and G4 correction sequence
are instantiated internally from smooth bracket generation. -/
theorem exists_canonical_ordinary_control_cost {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 1 ≤ s)
    (hw : ∀ i, (p i : ℕ) ≤ s)
    {Ω : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω p X s)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :
    ∃ r A : ℝ, 0 < r ∧ r ≤ C.radius ∧ 0 < A ∧
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
      controlDistance Ω p X η ξ ≤ ENNReal.ofReal
        (A * rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))) := by
  have hxΩ : x ∈ Ω := C.closedPatch_subset (mem_closedBall_self C.radius_pos.le)
  obtain ⟨R,A,ε,hR,_hRΩ,hA,hε,he⟩ :=
    G4.exists_smooth_ordinary_auxiliary_metric_comparison D.group.dimension_pos
      hs p hw hΩ X hX hstep hxΩ
  obtain ⟨r,hr,hrC,hg⟩ := C.exists_small_gauge_patch D.group hε
  refine ⟨min r (R/2),A,lt_min hr (by positivity),
    (min_le_left _ _).trans hrC,hA,?_⟩
  intro η hη ξ hξ
  have hηr : η ∈ ball x r := ball_subset_ball (min_le_left _ _) hη
  have hξr : ξ ∈ ball x r := ball_subset_ball (min_le_left _ _) hξ
  have hηC := ball_subset_ball hrC hηr
  have hξC := ball_subset_ball hrC hξr
  have hc := auxiliaryDistance_le_canonical_gauge D X C hηC hξC
  have hg' := hg η hηr ξ hξr
  have hsmall := hc.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr hg')
  have hd := (he η (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hη))
    ξ (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hξ)) hsmall).2
  calc
    controlDistance Ω p X η ξ ≤ ENNReal.ofReal A * G4.auxiliaryDistance (s := s) Ω p X η ξ := hd
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal
        (rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))) := by gcongr
    _ = _ := (ENNReal.ofReal_mul hA.le).symm
end RothschildStein.L1
