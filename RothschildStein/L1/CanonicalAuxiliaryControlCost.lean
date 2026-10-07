-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalControlledTrajectory
public import RothschildStein.L1.CanonicalShortFrame
public import RothschildStein.G4.AuxiliaryControl
public import RothschildStein.G2.MaxGauge
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- Canonical homogeneous weights as positive control weights. -/
def canonicalControlWeight {a s : ℕ} {p : Fin a → ℕ+} (D : G3.FreeModelData a s p)
    (j : Fin (freeDimension a s p)) : ℕ+ := ⟨D.group.weight j,D.group.weight_pos j⟩

/-- The actual canonical chart trajectory embeds into the complete
short-control family without changing its coefficient budget. -/
theorem auxiliaryDistance_canonicalFrameMap_le_of_parameters {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p)
    {Ω : Set (Fin (freeDimension a s p) → ℝ)}
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    {η u : Fin (freeDimension a s p) → ℝ}
    (hq : (C.time⁻¹ • u,η) ∈ ball (0,x) C.initialRadius)
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ j, |u j| ≤ δ^(D.group.weight j)) :
    G4.auxiliaryDistance (s := s) Ω p X η (canonicalFrameMap C.time C.flow (η,u)) ≤
      ENNReal.ofReal δ := by
  obtain ⟨γ, hac, hmap, hzero, hone, hd⟩ := C.exists_canonical_controlled_trajectory_of_parameters hq
  have hconst : G4.IsConstantControlledCurve Ω (canonicalControlWeight D)
      (canonicalWordFrame D X) δ γ := by
    refine ⟨hδ,hac,hmap,u,hb,?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hd t ht
  let e := fun j => Fintype.equivFin (G4.ShortWord p s) (canonicalShortWord D j)
  have he : Function.Injective e := (Fintype.equivFin _).injective.comp
    (canonicalShortWord_injective D)
  have hγ : isControlledCurve Ω
      (fun j => G4.shortWeight p (G4.shortIndex (s := s) p j))
      (fun j => G4.shortField p X (G4.shortIndex (s := s) p j)) δ γ :=
    G4.isControlledCurve_extend e he
    (fun j => by
      apply Subtype.ext
      simp only [e,G4.shortIndex,Equiv.symm_apply_apply]
      exact canonicalShortWord_weight D j)
    (fun j => by
      simp only [e,G4.shortIndex,Equiv.symm_apply_apply]
      exact (canonicalWordFrame_eq_shortField D X j).symm) hconst.isControlledCurve
  have hcost := G1.controlDistance_le_of_curve hγ
  rw [hzero,hone] at hcost
  exact hcost

/-- The max homogeneous gauge supplies exactly the weighted coefficient budget. -/
theorem canonical_gauge_coefficient_budget {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p) (u : Fin (freeDimension a s p) → ℝ) :
    ∀ j, |u j| ≤ (rsGauge D.group.weight D.group.weight_pos u)^(D.group.weight j) := by
  intro j
  have hh := G2.coordinate_root_le_gauge D.group u j
  have hpos : 0 < (D.group.weight j : ℝ) := Nat.cast_pos.mpr (D.group.weight_pos j)
  have hb := (Real.rpow_inv_le_iff_of_pos (abs_nonneg (u j))
    (G2.gauge_nonneg D.group u) hpos).mp hh
  simpa only [Real.rpow_natCast] using hb
/-- The canonical gauge bounds the actual auxiliary distance on the
inverse chart patch, using its actual flow and inverse identities. -/
theorem auxiliaryDistance_le_canonical_gauge {a s : ℕ} {p : Fin a → ℕ+}
    (D : G3.FreeModelData a s p)
    {Ω : Set (Fin (freeDimension a s p) → ℝ)}
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    {η ξ : Fin (freeDimension a s p) → ℝ}
    (hη : η ∈ ball x C.radius) (hξ : ξ ∈ ball x C.radius) :
    G4.auxiliaryDistance (s := s) Ω p X η ξ ≤
      ENNReal.ofReal (rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))) := by
  have hp : (η,ξ) ∈ C.inverseDomain := C.basePatch_subset ⟨hη,hξ⟩
  by_cases hz : rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) = 0
  · have hu := (G2.gauge_eq_zero_iff D.group _).mp hz
    have hηi : η ∈ ball x C.initialRadius :=
      ball_subset_ball C.radius_le_initial hη
    have ht : C.time ∈ Ioo (-C.timeRadius) C.timeRadius :=
      ⟨by linarith [C.timeRadius_pos,C.time_pos],C.time_lt⟩
    have hξeq : ξ = η := by
      have hh := C.right_inverse (η,ξ) hp
      simpa [canonicalFrameMap,hu,C.flow_zero η hηi C.time ht] using hh.symm
    subst ξ
    change controlDistance Ω _ _ η η ≤ _
    rw [G1.controlDistance_self _ _ (C.closedPatch_subset (ball_subset_closedBall hη))]
    exact bot_le
  · have hpos := lt_of_le_of_ne (G2.gauge_nonneg D.group (C.theta (η,ξ))) (Ne.symm hz)
    have hh := auxiliaryDistance_canonicalFrameMap_le_of_parameters D X C
      (C.inverse_parameters (η,ξ) hp) hpos
      (canonical_gauge_coefficient_budget D (C.theta (η,ξ)))
    rwa [C.right_inverse (η,ξ) hp] at hh
end RothschildStein.L1
