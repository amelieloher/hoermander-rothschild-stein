-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CoordinateApproximationData
public import RothschildStein.L1.ModelShortFrame
public import RothschildStein.L1.FreeAmbientVolumeUnconditional

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.L1.CoordinateApproximationData

/-- For the fixed lift and coordinate data, both
ambient ball volumes have the exact chosen model exponent, uniformly
on every compact center set. Smoothness, freeness, the ambient-domain
comparison and exponent identification are constructed internally
(BB Cor. 10.37 and Thm. 10.40, pp. 515–522). -/
theorem compact_power_ball_volumes {n k s m : ℕ} {w : Fin (k+1) → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ cv Cv cvStar CvStar rstar : ℝ,
      0 < cv ∧ 0 < Cv ∧ 0 < cvStar ∧ 0 < CvStar ∧ 0 < rstar ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r ≤ rstar →
        ENNReal.ofReal (cv*r^M.G.homogeneousDimension) ≤
          volume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r) ∧
        volume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r) ≤
          ENNReal.ofReal (Cv*r^M.G.homogeneousDimension) ∧
        ENNReal.ofReal (cvStar*r^M.G.homogeneousDimension) ≤
          volume {ξ ∈ basePoint ⁻¹' Ω | G4.auxiliaryDistance (s := s)
            (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ < ENNReal.ofReal r} ∧
        volume {ξ ∈ basePoint ⁻¹' Ω | G4.auxiliaryDistance (s := s)
          (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ < ENNReal.ofReal r} ≤
          ENNReal.ofReal (CvStar*r^M.G.homogeneousDimension) := by
  classical
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1,1,1,1,1,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    intro η hη
    simp only [he,mem_empty_iff_false] at hη
  have hAU : A.U ⊆ (L.U : Set _) := fun _ hξ => A.closure_subset_lift (subset_closure hξ)
  have hAO : A.U ⊆ basePoint ⁻¹' Ω := hAU.trans L.subset_domain
  have hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X L.P i) A.U :=
    fun i => (L.smooth i).mono hAO
  have hstep : bracketStepOn A.U w (triangularLift X L.P) s :=
    fun η hη => (L.free_spanning η (hAU hη)).2
  have hFree : ∀ η ∈ K, FreeAt w s (triangularLift X L.P) η :=
    fun η hη => (L.free_spanning η (hAU (hKU hη))).1
  obtain ⟨η₀,hη₀⟩ := hne
  obtain ⟨B,hB,cv,Cv,cvStar,CvStar,rstar,hcv,hCv,hcvStar,hCvStar,hrstar,hv⟩ :=
    exists_free_ambient_ball_volume_package M.G.dimension_pos hs A.isOpen_U hK hKU
      w hw (triangularLift X L.P) hZ hstep hFree hη₀
  have hQ := M.frame_weight_sum_eq_homogeneousDimension ⟨A.U,A.isOpen_U⟩
    (triangularLift X L.P) hZ (hKU hη₀) (hFree η₀ hη₀) B hB
  refine ⟨cv,Cv,cvStar,CvStar,rstar,hcv,hCv,hcvStar,hCvStar,hrstar,?_⟩
  intro η hη r hr hrr
  simpa only [hQ] using hv (basePoint ⁻¹' Ω) hAO η hη r hr hrr

/-- The exact real-valued power-volume clause of
GaugeFiberData.ball_bounds, for any fixed coordinate data.
Finiteness and positivity are derived from the measured power bounds
(BB pp. 515–516, 521–522). -/
theorem compact_real_power_ball_volumes {n k s m : ℕ} {w : Fin (k+1) → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ rstar cv Cv : ℝ, 0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r
        volume Ul ≠ ⊤ ∧ 0 < (volume Ul).toReal ∧
        cv*r^M.G.homogeneousDimension ≤ (volume Ul).toReal ∧
        (volume Ul).toReal ≤ Cv*r^M.G.homogeneousDimension := by
  obtain ⟨cv,Cv,_cvStar,_CvStar,rstar,hcv,hCv,_hcvStar,_hCvStar,hrstar,hv⟩ :=
    A.compact_power_ball_volumes hs hw hK hKU
  refine ⟨rstar,cv,Cv,hrstar,hcv,hCv,?_⟩
  intro η hη r hr hrr Ul
  have hh := hv η hη r hr hrr.le
  have hfin : volume Ul ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh.2.1
  have hlo := ENNReal.toReal_mono hfin hh.1
  have hhi := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh.2.1
  rw [ENNReal.toReal_ofReal (by positivity)] at hlo hhi
  exact ⟨hfin,(mul_pos hcv (pow_pos hr _)).trans_le hlo,hlo,hhi⟩

end RothschildStein.L1.CoordinateApproximationData
