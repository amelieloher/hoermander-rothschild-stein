-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.StarredFiberUniformConstants
public import RothschildStein.L1.StarredFiberSingleScale
public import RothschildStein.L1.CoordinateFrameCompletion
public import RothschildStein.L1.CoordinateBallDensityFacts
public import RothschildStein.L1.CompletedFrameBallMeasureRatio

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- The single-scale fiber
bounds for starred balls, uniform over every compact set of centres in the
coordinate patch, follow from the paired compact chart buffers: the completion
threshold `t` of `exists_uniform_completed_frame`, common radii for the finitely
many chart families, the single-scale bound at each centre and radius, and the
completed-frame ball-volume ratio. -/
theorem CoordinateApproximationData.starredFiberBounds_of_chartBuffers {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s) (hbuf : CompactChartBuffers A) :
    StarredFiberBounds A := by
  intro K hK hKU
  obtain ⟨t,ht,ht1,hcomp⟩ := A.exists_uniform_completed_frame hΩ hX hK hKU
  obtain ⟨N,zo,zl,Fo,Fl,hcov,a,bo,bl,r₁,ha,ha1,hbo,hboa,hbl,hr₁,hgeo⟩ :=
    A.exists_starredFiber_uniform_chart_data hbuf ht ht1 hK hKU
  have hKL : K ⊆ (L.U : Set (Fin (n + m) → ℝ)) := fun ξ hξ =>
    A.closure_subset_lift (subset_closure (hKU hξ))
  have hUoΩ : (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) ⊆ Ω := by
    rintro x ⟨ξ,hξ,rfl⟩
    exact L.subset_domain hξ
  have hUlΩ : (L.U : Set (Fin (n + m) → ℝ)) ⊆ basePoint ⁻¹' Ω := L.subset_domain
  have hstepo := L.original_bracketStepOn_image hΩ hX
  have hstepl : bracketStepOn (L.U : Set (Fin (n + m) → ℝ)) w (triangularLift X L.P) s :=
    fun ξ hξ => (L.free_spanning ξ hξ).2
  have hKUo : basePoint '' K ⊆
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) :=
    image_mono hKL
  obtain ⟨cv,Cv,rv,hcv,hCv,hrv,hratio⟩ := exists_completed_frame_ball_measure_ratio hn hs w hw
    (isOpen_basePoint_image L.U.isOpen) L.U.isOpen hK hKL hKUo X L.P
    (fun i => (hX i).mono hUoΩ) (fun i => (L.smooth i).mono hUlΩ) hstepo hstepl ht
  obtain ⟨rstar,_cvol,_Cvol,hrstar,_hcvol,_hCvol,hfacts⟩ :=
    A.compact_ball_density_facts hΩ hs hw hK hKU
  refine ⟨min (min r₁ rv) (rstar / 2),bo,bl * bo / a,a,2 ^ m * bo ^ (m * s) / 16 / Cv,
    16 * 2 ^ m / cv,lt_min (lt_min hr₁ hrv) (half_pos hrstar),hbo,by positivity,ha,
    by positivity,by positivity,?_⟩
  intro η hη δ hδ hδr H y hy
  obtain ⟨i,hηo,hηl⟩ := hcov η hη
  obtain ⟨haFo,haFl,hro,hrl,hgo,hgl⟩ := hgeo i
  have hδ1 : δ ≤ r₁ := hδr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ rv := hδr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ < rstar := lt_of_le_of_lt (hδr.trans (min_le_right _ _)) (half_lt_self hrstar)
  obtain ⟨_hsub,_hmu,_hmv,hfu,hfv,_hpu,hpv,_hlo,_hhi,_hproj⟩ := hfacts η hη δ hδ hδ3
  have hsingle := L.starredFiber_single_scale hΩ hX (hKL hη)
    (fun B hB => hcomp η hη B hB) (Fo i) (Fl i) hηo hηl ha ha1 haFo haFl hbo hboa hcv hCv
    hgo hgl hδ (hδ1.trans hro) (hδ1.trans hrl) hfv hfu hpv
    (fun B J hB ho hl => hratio Ω hUoΩ hUlΩ η hη δ hδ hδ2 B J hB ho hl)
  exact hsingle y hy

end RothschildStein.L1
