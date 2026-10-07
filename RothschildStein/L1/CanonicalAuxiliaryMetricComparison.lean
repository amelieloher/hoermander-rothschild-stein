-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalBallBoxGaugeBound
public import RothschildStein.L1.CanonicalGaugeSmallPatch
public import RothschildStein.G1.ControlSeparation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- The actual canonical gauge and auxiliary distance are
comparable on a common spatial patch, with no comparison hypothesis. -/
theorem exists_canonical_auxiliary_metric_comparison {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 0 < s)
    {Ω : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω p X s) (hFree : ∀ y ∈ Ω, FreeAt p s X y)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :
    ∃ r A : ℝ, 0 < r ∧ r ≤ C.radius ∧ 0 < A ∧
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
      let ρ := rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))
      G4.auxiliaryDistance (s := s) Ω p X η ξ ≤ ENNReal.ofReal ρ ∧
      ENNReal.ofReal ρ ≤ ENNReal.ofReal A * G4.auxiliaryDistance (s := s) Ω p X η ξ := by
  obtain ⟨R,A,ε,hR,hRC,hA,hε,he⟩ :=
    exists_canonical_ball_box_gauge_bound D hs hΩ X hX hstep hFree C
  obtain ⟨r,hr,hrC,hg⟩ := C.exists_small_gauge_patch D.group (half_pos hε)
  refine ⟨min R r,2*A,lt_min hR hr,(min_le_left _ _).trans hRC,by positivity,?_⟩
  intro η hη ξ hξ
  have hηR := ball_subset_ball (min_le_left R r) hη
  have hηC := ball_subset_ball hRC hηR
  have hξC := ball_subset_ball hrC (ball_subset_ball (min_le_right R r) hξ)
  have hc := auxiliaryDistance_le_canonical_gauge D X C hηC hξC
  refine ⟨hc,?_⟩
  let d := G4.auxiliaryDistance (s := s) Ω p X η ξ
  have hdt : d ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc
  by_cases hzero : d = 0
  · have hηΩ := C.closedPatch_subset (ball_subset_closedBall hηC)
    have heq : η = ξ := (G1.controlDistance_eq_zero_iff hΩ
      (fun j => G4.shortWeight p (G4.shortIndex (s := s) p j))
      (fun j => G4.shortField p X (G4.shortIndex (s := s) p j))
      (fun j => (G4.shortField_contDiffOn hΩ hX _).continuousOn) hηΩ).mp hzero
    subst ξ
    rw [C.theta_diagonal η hηC,(G2.gauge_eq_zero_iff D.group 0).mpr rfl,ENNReal.ofReal_zero]
    exact bot_le
  · have hdpos := ENNReal.toReal_pos hzero hdt
    have hsmall := hg η (ball_subset_ball (min_le_right R r) hη)
      ξ (ball_subset_ball (min_le_right R r) hξ)
    have hdsmall : d.toReal < ε/2 := by
      have hh := (ENNReal.toReal_lt_toReal hdt ENNReal.ofReal_ne_top).mpr
        (hc.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hsmall))
      simpa only [ENNReal.toReal_ofReal (half_pos hε).le] using hh
    have hcost := he η hηR ξ (2*d.toReal) (by positivity) (by linarith) (by
      change d < ENNReal.ofReal (2*d.toReal)
      calc
        d = ENNReal.ofReal d.toReal := (ENNReal.ofReal_toReal hdt).symm
        _ < ENNReal.ofReal (2*d.toReal) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2*d.toReal)).mpr (by linarith))
    calc
      ENNReal.ofReal (rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))) ≤
          ENNReal.ofReal (A*(2*d.toReal)) := ENNReal.ofReal_le_ofReal hcost
      _ = ENNReal.ofReal (2*A)*d := by
        rw [show A*(2*d.toReal) = (2*A)*d.toReal by ring,
          ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hdt]
end RothschildStein.L1
