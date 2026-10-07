-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.StarredFiberGeometry
public import RothschildStein.L1.StarredFiberChartData
public import RothschildStein.L1.CompletedFamilyBoxProjection
public import RothschildStein.L1.JoinedFrameFiberDensity
public import RothschildStein.L1.ProjectedFreePatch
public import RothschildStein.G1.ActualControlComparison
public import RothschildStein.L1.FixedLiftData
public import RothschildStein.G4.FrameVolumeAdapters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
open RothschildStein.L1.StarredFiber
namespace RothschildStein.L1.FixedLiftData

/-- Single-centre, single-scale
fiber bounds for starred balls. At one centre `η` of the free patch and one
radius `δ`, a `1/2`-suboptimal original frame `B` at `(basePoint η, δ)`, its
uniformly suboptimal completion `J`, the actual shifted original and
zero-shift lifted charts of paired chart families (with radii
`a`, `bo`, `bl`) and the completed-frame ball-volume ratio
bound the fiber volume of the lifted starred balls of radii `a δ` (lower
bound) and `(bl bo / a) δ` (upper bound) over the original starred ball of
radius `bo δ`, normalised by the ordinary ball quotient `H`. -/
theorem starredFiber_single_scale {n k s m : ℕ} {w : Fin (k+1) → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {η : Fin (n + m) → ℝ} (hη : η ∈ (L.U : Set (Fin (n + m) → ℝ)))
    {t : ℝ}
    (hcomp : ∀ B : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) B (basePoint η) ≠ 0 →
      ∃ J : Fin m → G4.ShortWord w s,
        G4.frameDet (G4.shortField w (triangularLift X L.P)) (completedFrame B J) η ≠ 0 ∧
        ∀ r : ℝ, 0 < r → G4.IsSuboptimal (G4.shortField w (triangularLift X L.P))
          (G4.shortWeight w) (completedFrame B J) η t r)
    {zo : Fin n → ℝ} {zl : Fin (n + m) → ℝ}
    (Fo : JointShortChartFamily (s := s) w
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) X zo (1/2))
    (Fl : JointShortChartFamily (s := s) w (L.U : Set (Fin (n + m) → ℝ))
      (triangularLift X L.P) zl t)
    (hηo : basePoint η ∈ closedBall zo (Fo.R / 16)) (hηl : η ∈ closedBall zl (Fl.R / 16))
    {a bo bl cv Cv : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/2)
    (haFo : a ≤ Fo.a₀) (haFl : a ≤ Fl.a₀)
    (hbo : 0 < bo) (hboa : bo ≤ a/8) (hcv : 0 < cv) (hCv : 0 < Cv)
    (hgo : ShiftedGeometry Fo a bo) (hgl : ZeroShiftGeometry Fl a bl)
    {δ : ℝ} (hδ : 0 < δ) (hδo : δ ≤ Fo.r₀) (hδl : δ ≤ Fl.r₀)
    (hA : volume (rsBall Ω w X (basePoint η) δ) ≠ ⊤)
    (hB : volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
      (triangularLift X L.P) η δ) ≠ ⊤)
    (hpos : 0 < (volume (rsBall Ω w X (basePoint η) δ)).toReal)
    (hratio : ∀ (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s),
      G4.frameDet (G4.shortField w X) B (basePoint η) ≠ 0 →
      G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B (basePoint η) (1/2) δ →
      G4.IsSuboptimal (G4.shortField w (triangularLift X L.P)) (G4.shortWeight w)
        (completedFrame B J) η t δ →
      let R := (|G4.frameDet (G4.shortField w (triangularLift X L.P)) (completedFrame B J) η| /
        |G4.frameDet (G4.shortField w X) B (basePoint η)|) *
          δ ^ G4.frameWeight (G4.shortWeight w) J
      let H := volume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η δ) /
        volume (rsBall Ω w X (basePoint η) δ)
      ENNReal.ofReal cv * ENNReal.ofReal R ≤ H ∧ H ≤ ENNReal.ofReal Cv * ENNReal.ofReal R) :
    let H := (volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
        (triangularLift X L.P) η δ)).toReal /
      (volume (rsBall Ω w X (basePoint η) δ)).toReal
    ∀ y : Fin n → ℝ,
      G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
        (basePoint η) y < ENNReal.ofReal (bo * δ) →
      ENNReal.ofReal ((2 ^ m * bo ^ (m * s) / 16 / Cv) * H) ≤
        fiberVolume {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
          (triangularLift X L.P) η ξ < ENNReal.ofReal (a * δ)} y ∧
      fiberVolume {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
          (triangularLift X L.P) η ξ < ENNReal.ofReal ((bl * bo / a) * δ)} y ≤
        ENNReal.ofReal ((16 * 2 ^ m / cv) * H) := by
  intro H y hy
  have hUoΩ : (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) ⊆ Ω := by
    rintro x ⟨ξ,hξ,rfl⟩
    exact L.subset_domain hξ
  have hUlΩ : (L.U : Set (Fin (n + m) → ℝ)) ⊆ basePoint ⁻¹' Ω := L.subset_domain
  have hUoopen : IsOpen (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) :=
    isOpen_basePoint_image L.U.isOpen
  have hstepo := L.original_bracketStepOn_image hΩ hX
  have hηUo : basePoint η ∈ (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) :=
    ⟨η,hη,rfl⟩
  -- the original `1/2`-suboptimal frame and its completion
  obtain ⟨B₀,hB₀⟩ := G4.exists_short_frame hstepo hηUo
  obtain ⟨B,hBsub⟩ := G4.exists_suboptimal_frame (G4.shortField w X) (G4.shortWeight w)
    (x := basePoint η) (t := 1/2) (r := δ) (by norm_num) hδ ⟨B₀,hB₀⟩
  have hBdet := G4.suboptimal_frame_ne_zero (by norm_num) hδ ⟨B₀,hB₀⟩ hBsub
  obtain ⟨J,hJdet,hJsub⟩ := hcomp B hBdet
  have hboa' : bo ≤ a := by linarith
  -- chart data of the two families
  obtain ⟨hFcd,hFinj,hFdet,hsmall,hlarge⟩ :=
    lifted_chart_data Fl hηl ha hbo hboa' hδ hδl hgl B J hJsub
  have hshift : ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (bo * δ),
      completionShift w J v ∈ G4.weightedBox
        (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j)) (bo * δ) := fun v hv =>
    completionShift_mem_weightedBox_of_frameDet_ne_zero w B J
      (G4.shortField w (triangularLift X L.P)) η hJdet (mul_pos hbo hδ) hv
  obtain ⟨hinj,hcover,hHdet⟩ := shifted_chart_data Fo hηo hδ hδo hgo B hBsub J hshift
  -- joined and mixed coordinates
  have hmixed : ∀ u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a * δ),
      ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (bo * δ),
      joinPoint u v ∈ G4.weightedBox (G4.shortWeight w ∘ completedFrame B J) (a * δ) := by
    intro u hu v hv
    rw [joinPoint_eq_append]
    exact completed_selected_parameters_mem_box w B J ha.le hbo.le hδ.le le_rfl hboa' hu hv
  have hproj : ∀ u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a * δ),
      ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (bo * δ),
      basePoint (liftedChart Fl B J η (joinPoint u v)) =
        shiftedChart Fo B J (basePoint η) u v := by
    intro u hu v hv
    rw [joinPoint_eq_append]
    exact completed_family_box_projection hΩ hUoΩ hUlΩ X hX L.P Fo Fl B J η hηo hηl hJdet
      (al := a) (au := a) (av := bo) (b := bo) (r := δ) ha haFl ha haFo hbo le_rfl hboa' le_rfl
      hboa' hδ hδl hδo hu hv
  have hdbase : 0 < |G4.frameDet (G4.shortField w X) B (basePoint η)| := abs_pos.mpr hBdet
  have hdlift : 0 ≤ |G4.frameDet (G4.shortField w (triangularLift X L.P))
      (completedFrame B J) η| := abs_nonneg _
  -- the completed-frame measure ratio in the adapter's format
  have hR : (|G4.frameDet (G4.shortField w (triangularLift X L.P)) (completedFrame B J) η| /
      |G4.frameDet (G4.shortField w X) B (basePoint η)|) *
        δ ^ G4.frameWeight (G4.shortWeight w) J =
      (|G4.frameDet (G4.shortField w (triangularLift X L.P)) (completedFrame B J) η| /
      |G4.frameDet (G4.shortField w X) B (basePoint η)|) *
        δ ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) := by
    rw [G4.frameWeight_eq_nat_sum, zpow_natCast]
    try rfl
  have hrat := hratio B J hBdet hBsub (hJsub δ hδ)
  simp only [hR] at hrat
  have hW : IsOpen {y | G4.auxiliaryDistance (s := s)
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) w X (basePoint η) y <
        ENNReal.ofReal (bo * δ)} :=
    isOpen_auxiliaryBall hUoopen (fun i => (hX i).mono hUoΩ) hstepo _ _
  have key := fiber_density_bounds_of_joined_weighted_frame_chart (n := n) (m := m)
    (D := G4.weightedBox (G4.shortWeight w ∘ completedFrame B J) (a * δ))
    (U := G4.weightedBox (G4.shortWeight w ∘ B) (a * δ))
    (W := {y | G4.auxiliaryDistance (s := s)
      (basePoint (n := n) (m := m) '' (L.U : Set (Fin (n + m) → ℝ))) w X (basePoint η) y <
        ENNReal.ofReal (bo * δ)})
    (V := G4.weightedBox (G4.shortWeight w ∘ J) (bo * δ))
    (G4.isOpen_weightedBox _ _) (G4.isOpen_weightedBox _ _) hW (G4.isOpen_weightedBox _ _)
    (liftedChart Fl B J η) (shiftedChart Fo B J (basePoint η))
    hFcd hFinj hmixed hproj hinj hcover
    (a := 1/4) (b := 4) (c := 1/4) (d := 4)
    (dlift := |G4.frameDet (G4.shortField w (triangularLift X L.P)) (completedFrame B J) η|)
    (dbase := |G4.frameDet (G4.shortField w X) B (basePoint η)|) (cv := cv) (Cv := Cv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdlift hdbase hcv hCv
    (fun p hp => by have := (hFdet p hp).1; linarith)
    (fun p hp => by have := (hFdet p hp).2; linarith)
    (fun u hu v hv => by have := (hHdet u hu v hv).1; linarith)
    (fun u hu v hv => by have := (hHdet u hu v hv).2; linarith)
    (G4.shortWeight w ∘ J) hbo.le hδ.le (fun _ h => h) hsmall hlarge
    (rsBall Ω w X (basePoint η) δ)
    (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η δ)
    hA hB hpos hrat y hy
  have hwS : ∀ J : G4.ShortWord w s, (G4.shortWeight w J : ℕ) ≤ s := fun J =>
    ((G4.mem_shortWordFamily_iff w J.val).mp J.property).2
  have hS : ∑ i, ((G4.shortWeight w ∘ J) i : ℕ) ≤ m * s :=
    G4.frame_natural_weight_le (G4.shortWeight w) hwS J
  have hbo1 : bo ≤ 1 := by linarith
  have hpow_lo : bo ^ (m * s) ≤ bo ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) :=
    pow_le_pow_of_le_one hbo.le hbo1 hS
  have hpow_hi : bo ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) ≤ 1 :=
    pow_le_one₀ hbo.le hbo1
  have hH : 0 ≤ H := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hPm : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) key.1, key.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  · calc (2 ^ m * bo ^ (m * s) / 16 / Cv) * H
        ≤ (2 ^ m * bo ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) / 16 / Cv) * H := by
          apply mul_le_mul_of_nonneg_right _ hH
          apply div_le_div_of_nonneg_right _ hCv.le
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hpow_lo hPm.le
      _ = _ := by
          simp only [H]
          ring
  · calc _ = (16 * 2 ^ m * bo ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) / cv) * H := by
          simp only [H]
          ring
      _ ≤ (16 * 2 ^ m / cv) * H := by
          apply mul_le_mul_of_nonneg_right _ hH
          apply div_le_div_of_nonneg_right _ hcv.le
          calc 16 * 2 ^ m * bo ^ (∑ i, ((G4.shortWeight w ∘ J) i : ℕ)) ≤ 16 * 2 ^ m * 1 :=
              mul_le_mul_of_nonneg_left hpow_hi (by positivity)
            _ = 16 * 2 ^ m := mul_one _

end RothschildStein.L1.FixedLiftData
