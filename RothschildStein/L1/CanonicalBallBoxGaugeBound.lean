-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartEndpointAgreement
public import RothschildStein.L1.CanonicalGaugeChartImage
public import RothschildStein.L1.CompactFreeGeometry
public import RothschildStein.L1.FrameIndependence
public import RothschildStein.G4.SmoothShortBallBoxProvider
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- The actual smooth ball-box chart gives a reverse canonical
gauge bound. Freeness supplies uniform suboptimality of the canonical
frame; actual trajectory uniqueness identifies the two flow charts. -/
theorem exists_canonical_ball_box_gauge_bound {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 0 < s)
    {Ω : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω p X s) (hFree : ∀ y ∈ Ω, FreeAt p s X y)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x) :
    ∃ R A ε : ℝ, 0 < R ∧ R ≤ C.radius ∧ 0 < A ∧ 0 < ε ∧
      ∀ η ∈ ball x R, ∀ ξ, ∀ r : ℝ, 0 < r → r ≤ ε →
      G4.auxiliaryDistance (s := s) Ω p X η ξ < ENNReal.ofReal r →
      rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ)) ≤ A*r := by
  classical
  have hCr := C.radius_pos
  let B := canonicalShortWord D
  have hxC : x ∈ ball x C.radius := mem_ball_self C.radius_pos
  have hxΩ : x ∈ Ω := C.closedPatch_subset (mem_closedBall_self C.radius_pos.le)
  have hKΩ : closedBall x (C.radius/2) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith [C.radius_pos])).trans C.closedPatch_subset
  have hBx : G4.frameDet (G4.shortField p X) B x ≠ 0 := by
    apply (frameDet_ne_zero_iff_linearIndependent _ _ _).mpr
    simpa only [B,← canonicalWordFrame_eq_shortField] using C.frame x hxC
  obtain ⟨t,ht,ht1,hsub⟩ := exists_uniform_short_suboptimality_of_FreeAt hΩ
    (isCompact_closedBall x (C.radius/2)) hKΩ p X hX
    (fun y hy => hFree y (hKΩ hy)) (mem_closedBall_self (by positivity)) B hBx
  have ht' : 0 < t/2 := by positivity
  have ht1' : t/2 < 1 := by linarith
  obtain ⟨R₀,hR₀,_hR₀Ω,a,b,r₀,M,κ,ha,ha1,hb,_hba,_hb1,
    hr₀,_hr₀1,_hM,_hκ,_hnκ,Φ,hΦ⟩ :=
    G4.exists_smooth_short_ball_box_provider D.group.dimension_pos hs p ht' ht1'
      hΩ X hX hstep hxΩ
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (canonicalWordFrame D X i) Ω := by
    intro i
    simpa only [canonicalWordFrame_eq_shortField] using
      G4.shortField_contDiffOn hΩ hX (B i)
  obtain ⟨ε₀,hε₀,he⟩ := C.exists_chart_endpoint_agreement hY (canonicalControlWeight D)
  let R := min (R₀/16) (C.radius/4)
  let q := min r₀ (min (ε₀/2) (min (C.radius/2) 1))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hq : 0 < q := lt_min hr₀ (lt_min (by positivity) (lt_min (by positivity) zero_lt_one))
  refine ⟨R,a/b,b*q,hR,by dsimp [R]; linarith [min_le_right (R₀/16) (C.radius/4)],
    div_pos ha hb,mul_pos hb hq,?_⟩
  intro η hη ξ r hr hrε hd
  have hηR₀ : η ∈ closedBall x (R₀/16) :=
    ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hη)
  have hηhalf : η ∈ ball x (C.radius/2) :=
    ball_subset_ball (by dsimp [R]; linarith [min_le_right (R₀/16) (C.radius/4)]) hη
  have hηC : η ∈ ball x C.radius := ball_subset_ball (by linarith [C.radius_pos]) hηhalf
  have hηK : η ∈ closedBall x (C.radius/2) := ball_subset_closedBall hηhalf
  have hBr : G4.frameDet (G4.shortField p X) B η ≠ 0 := by
    apply (frameDet_ne_zero_iff_linearIndependent _ _ _).mpr
    simpa only [B,← canonicalWordFrame_eq_shortField] using C.frame η hηC
  have hrb : 0 < r/b := div_pos hr hb
  have hrbq : r/b ≤ q := (div_le_iff₀ hb).mpr (by nlinarith)
  have hrbr₀ : r/b ≤ r₀ := hrbq.trans (min_le_left _ _)
  have hBt : G4.IsSuboptimal (G4.shortField p X) (G4.shortWeight p) B η (t/2) (r/b) := by
    intro J
    apply le_trans _ (hsub η hηK B hBr (r/b) hrb J)
    apply mul_le_mul_of_nonneg_right (by linarith : t/2 ≤ t)
    exact mul_nonneg (abs_nonneg _) (zpow_nonneg hrb.le _)
  have hzero : (0 : Fin (Fintype.card (G4.ShortWord p s)) → ℝ) ∈
      G4.weightedBox (fun j => G4.shortWeight p (G4.shortIndex p j)) (b*(r/b)) := by
    intro j
    simp only [Pi.zero_apply,abs_zero]
    exact pow_pos (mul_pos hb hrb) _
  obtain ⟨_han,htraj,_hinit,_hinj,_hjac,hin,_hrest⟩ :=
    hΦ η hηR₀ (r/b) hrb hrbr₀ B hBt 0 hzero
  let F := fun u => Φ B ((Fin.append u 0,η),1)
  let v := a*(r/b)
  have hv : 0 < v := mul_pos ha hrb
  have hva : v ≤ r/b := mul_le_of_le_one_left hrb.le ha1.le
  have hve : v < ε₀ := by
    have hh := hrbq.trans ((min_le_right r₀ _).trans (min_le_left _ _))
    dsimp [v] at hva ⊢
    linarith
  have hvC : v ≤ C.radius := by
    have hh := hrbq.trans ((min_le_right r₀ _).trans ((min_le_right (ε₀/2) _).trans (min_le_left _ _)))
    linarith
  have hv1 : v ≤ 1 := hva.trans (hrbq.trans ((min_le_right r₀ _).trans
    ((min_le_right (ε₀/2) _).trans (min_le_right _ _))))
  have hwB : G4.shortWeight p ∘ B = canonicalControlWeight D := by
    funext i
    apply Subtype.ext
    exact canonicalShortWord_weight D i
  have hF : EqOn F (fun u => canonicalFrameMap C.time C.flow (η,u))
      (G4.weightedBox (canonicalControlWeight D) v) := by
    intro u hu
    have huC := ball_subset_ball hvC
      (G4.weightedBox_subset_ball (canonicalControlWeight D) hv hv1 hu)
    apply he v hv hve η hηhalf u (C.coefficients (η,u) ⟨hηC,huC⟩).1
      (fun i => (hu i).le)
      (Fintype.card (G4.ShortWord p s))
      (fun j => G4.shortField p X (G4.shortIndex p j))
      ((Fintype.equivFin (G4.ShortWord p s)) ∘ B)
      (fun i => by
        simpa only [Function.comp_apply,G4.shortIndex,Equiv.symm_apply_apply]
          using (canonicalWordFrame_eq_shortField D X i).symm)
      F _ _ htraj
    simpa only [hwB] using hu
  have hbr : b*(r/b) = r := by field_simp
  have hd' : G4.auxiliaryDistance (s := s) Ω p X η ξ < ENNReal.ofReal (b*(r/b)) := by
    simpa only [hbr] using hd
  have hi : ξ ∈ F '' G4.weightedBox (canonicalControlWeight D) v := by
    simpa only [hwB] using hin hd'
  have hh := canonical_gauge_le_of_chart_image D C hηC hv hv1 hvC F hF hi
  have heq : v = (a/b)*r := by dsimp [v]; ring
  simpa only [heq] using hh
end RothschildStein.L1
