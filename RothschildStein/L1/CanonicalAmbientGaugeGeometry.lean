-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalAmbientDistanceEquality
public import RothschildStein.L1.CanonicalGaugeQuasiTriangleProvider
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- Both original ambient distances compare with the same actual
canonical gauge on one patch, which also has a quasi-triangle constant.
No ambient freeness or ambient bracket-rank hypothesis is added. -/
theorem exists_canonical_ambient_gauge_geometry {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 1 ≤ s)
    (hw : ∀ i, (p i : ℕ) ≤ s)
    {U : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hU : IsOpen U)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U p X s) (hFree : ∀ y ∈ U, FreeAt p s X y)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData U (canonicalWordFrame D X) x) :
    ∃ r A B T : ℝ, 0 < r ∧ r ≤ C.radius ∧ 0 < A ∧ 0 < B ∧ 1 ≤ T ∧
      (∀ Ω : Set (Fin (freeDimension (k+1) s p) → ℝ), U ⊆ Ω →
        ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
        let ρ := rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))
        G4.auxiliaryDistance (s := s) Ω p X η ξ ≤ ENNReal.ofReal ρ ∧
        ENNReal.ofReal ρ ≤ ENNReal.ofReal B * G4.auxiliaryDistance (s := s) Ω p X η ξ ∧
        controlDistance Ω p X η ξ ≤ ENNReal.ofReal (A*ρ) ∧
        ENNReal.ofReal ρ ≤ ENNReal.ofReal B * controlDistance Ω p X η ξ) ∧
      (∀ η ∈ ball x r, ∀ ξ ∈ ball x r, ∀ ζ ∈ ball x r,
        rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) ≤
          T*(rsGauge D.group.weight D.group.weight_pos (C.theta (η,ζ)) +
            rsGauge D.group.weight D.group.weight_pos (C.theta (ζ,ξ)))) := by
  obtain ⟨r₁,B,hr₁,hr₁C,hB,hmetric⟩ :=
    exists_canonical_auxiliary_metric_comparison D (by omega) hU X hX hstep hFree C
  obtain ⟨r₂,A,hr₂,_hr₂C,hA,hcost⟩ :=
    exists_canonical_ordinary_control_cost D hs hw hU X hX hstep C
  obtain ⟨r₃,T,hr₃,_hr₃C,hT,htri⟩ :=
    exists_canonical_gauge_quasi_triangle D (by omega) hU X hX hstep hFree C
  obtain ⟨r₄,hr₄,_hr₄C,heq⟩ :=
    exists_canonical_ambient_distance_equalities D hs hw hU X hX hstep C
  let r := min r₁ (min r₂ (min r₃ r₄))
  have hr : 0 < r := lt_min hr₁ (lt_min hr₂ (lt_min hr₃ hr₄))
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₃ : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrr₄ : r ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r,A,B,T,hr,hrr₁.trans hr₁C,hA,hB,hT,?_,?_⟩
  · intro Ω hUU η hη ξ hξ
    have hm := hmetric η (ball_subset_ball hrr₁ hη) ξ (ball_subset_ball hrr₁ hξ)
    have hc := hcost η (ball_subset_ball hrr₂ hη) ξ (ball_subset_ball hrr₂ hξ)
    have he := heq Ω hUU η (ball_subset_ball hrr₄ hη) ξ (ball_subset_ball hrr₄ hξ)
    dsimp only
    rw [he.1,he.2]
    refine ⟨hm.1,hm.2,hc,?_⟩
    exact hm.2.trans (by
      gcongr
      exact G4.auxiliaryDistance_le U p X hw η ξ)
  · intro η hη ξ hξ ζ hζ
    exact htri η (ball_subset_ball hrr₃ hη) ξ (ball_subset_ball hrr₃ hξ)
      ζ (ball_subset_ball hrr₃ hζ)
end RothschildStein.L1
