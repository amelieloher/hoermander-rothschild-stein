-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CoordinatePowerBallVolumes
public import RothschildStein.L1.PrefixDerivative
public import RothschildStein.L1.TriangularCoefficientDependence
public import RothschildStein.L1.TriangularExistence
public import RothschildStein.L1.MeasurableControlIntegration
public import RothschildStein.L1.CoordinateAbsoluteContinuity
public import RothschildStein.L1.TriangularBracketProjection

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- Two actual power-volume bounds compare an enlarged lifted
ball to the target ball, with its fixed enlargement factor explicit
(BB pp. 521–522, corrected fixed-factor rescaling). -/
theorem measure_enlargement_le_of_power_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (Bsmall Blarge : Set E) {cv Cv A r : ℝ} (hcv : 0 < cv)
    (hCv : 0 ≤ Cv) (hA : 0 ≤ A) (_hr : 0 ≤ r) (Q : ℕ)
    (hsmall : ENNReal.ofReal (cv*r^Q) ≤ μ Bsmall)
    (hlarge : μ Blarge ≤ ENNReal.ofReal (Cv*(A*r)^Q)) :
    μ Blarge ≤ ENNReal.ofReal ((Cv/cv)*A^Q) * μ Bsmall := by
  have he : ENNReal.ofReal (Cv*(A*r)^Q) =
      ENNReal.ofReal ((Cv/cv)*A^Q) * ENNReal.ofReal (cv*r^Q) := by
    rw [← ENNReal.ofReal_mul (by positivity),mul_pow]
    congr 1
    field_simp [hcv.ne']
  exact (hlarge.trans_eq he).trans (mul_le_mul_right hsmall _)

end RothschildStein.L1
namespace RothschildStein.L1.CoordinateApproximationData

/-- Uniform fixed-factor rescaling of the actual ordinary
lifted/original volume quotient for the fixed coordinate data. Both
inequalities follow from the constructed free power-volume bounds and
radius monotonicity; no doubling or quotient comparison is supplied
(BB pp. 521–522, explicit rescaling repair). -/
theorem compact_volume_ratio_rescaling {n k s m : ℕ} {w : Fin (k+1) → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (Adata : CoordinateApproximationData L M)
    (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ Adata.U) :
    ∃ rstar C : ℝ, 0 < rstar ∧ 0 < C ∧
      ∀ η ∈ K, ∀ A r : ℝ, 1 ≤ A → 0 < r → A*r ≤ rstar →
        let H := fun R : ℝ =>
          volume (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η R) /
            volume (rsBall Ω w X (basePoint η) R)
        H (A*r) ≤ ENNReal.ofReal (C*A^M.G.homogeneousDimension) * H r ∧
        ENNReal.ofReal (1/(C*A^M.G.homogeneousDimension)) * H r ≤ H (r/A) := by
  obtain ⟨cv,Cv,_cvStar,_CvStar,rstar,hcv,hCv,_hcvStar,_hCvStar,hrstar,hv⟩ :=
    Adata.compact_power_ball_volumes hs hw hK hKU
  refine ⟨rstar,Cv/cv,hrstar,div_pos hCv hcv,?_⟩
  intro η hη A r hA hr hAr H
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hrAr : r ≤ A*r := by nlinarith
  have hrr : r ≤ rstar := hrAr.trans hAr
  have hd : 0 < r/A := div_pos hr hAp
  have hdr : r/A ≤ r := (div_le_self hr.le hA)
  have hdeq : A*(r/A) = r := by field_simp [hAp.ne']
  have hbsmall := (hv η hη r hr hrr).1
  have hblarge := (hv η hη (A*r) (mul_pos hAp hr) hAr).2.1
  have hnum := measure_enlargement_le_of_power_bounds volume _ _ hcv hCv.le
    hAp.le hr.le M.G.homogeneousDimension hbsmall hblarge
  have hden : volume (rsBall Ω w X (basePoint η) r) ≤
      volume (rsBall Ω w X (basePoint η) (A*r)) :=
    measure_mono (fun _ hy => ⟨hy.1,hy.2.trans_le (ENNReal.ofReal_le_ofReal hrAr)⟩)
  have hu := ENNReal.div_le_div hnum hden
  have hnumb := measure_enlargement_le_of_power_bounds volume
    (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η (r/A))
    (rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r)
    hcv hCv.le hAp.le hd.le M.G.homogeneousDimension
    (hv η hη (r/A) hd (hdr.trans hrr)).1
    (by simpa only [hdeq] using (hv η hη r hr hrr).2.1)
  have hc : 0 < (Cv/cv)*A^M.G.homogeneousDimension := by positivity
  have hm := mul_le_mul_right hnumb (ENNReal.ofReal (1/((Cv/cv)*A^M.G.homogeneousDimension)))
  have he : ENNReal.ofReal (1/((Cv/cv)*A^M.G.homogeneousDimension)) *
      ENNReal.ofReal ((Cv/cv)*A^M.G.homogeneousDimension) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity),one_div_mul_cancel hc.ne',ENNReal.ofReal_one]
  rw [← mul_assoc,he,one_mul] at hm
  have hdenb : volume (rsBall Ω w X (basePoint η) (r/A)) ≤
      volume (rsBall Ω w X (basePoint η) r) :=
    measure_mono (fun _ hy => ⟨hy.1,hy.2.trans_le (ENNReal.ofReal_le_ofReal hdr)⟩)
  have hl := ENNReal.div_le_div hm hdenb
  constructor
  · simpa only [H,div_eq_mul_inv,mul_assoc] using hu
  · simpa only [H,div_eq_mul_inv,mul_assoc] using hl

end RothschildStein.L1.CoordinateApproximationData
