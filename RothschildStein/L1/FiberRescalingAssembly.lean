-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberRescalingBounds
public import RothschildStein.L1.FiberSupport
public import RothschildStein.L1.PowerVolumeRescaling
public import RothschildStein.L1.CoordinateBallDensityFacts

/-!
# Fixed-factor rescaling: the compact fiber clause

`CompactFiberBounds` for every coordinate data set, from the single-scale starred fiber
bounds and the compact starred comparison, by the corrected fixed-factor rescaling
(fixed-factor rescaling; BB pp. 521–522).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1.CoordinateApproximationData

/-- The compact fiber clause from the starred fiber bounds
and the starred comparison: enlarge the radius by the fixed factor `Λ` for the upper bound
and reduce it by the fixed factor `Λ'` for the lower bound, compare the ordinary ball
quotients with `compact_volume_ratio_rescaling`, and use that fibers vanish outside the
projected ball (BB pp. 521–522). -/
theorem compactFiberBounds_of_starred {n k s m : ℕ}
    {w : Fin (k+1) → ℕ+} {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hΩ : IsOpen Ω) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    (hstar : StarredFiberBounds A) (hcomp : CompactStarredComparison A) :
    CompactFiberBounds A := by
  intro K hK hKU
  obtain ⟨r₀, cw, cs, cl, cf, Cf, hr₀, hcw, hcs, hcl, hcf, hCf, hS⟩ := hstar K hK hKU
  obtain ⟨r₁, C, hr₁, hC, hcmp⟩ := hcomp K hK hKU
  obtain ⟨rr, C', hrr, hC', hresc⟩ := A.compact_volume_ratio_rescaling hs hw hK hKU
  obtain ⟨rd, cv, Cv, hrd, hcv, hCv, hfacts⟩ := A.compact_ball_density_facts hΩ hs hw hK hKU
  obtain ⟨Λ, Λ', δf, rs, hΛ, hΛ', hδf0, hδf1, hrs, hCw, hCs, hCl, hδ, hrad⟩ :=
    fiberRescaling_exists_scales hr₀ hcw hcs hcl hr₁ hC hrr hrd
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hΛ'0 : 0 < Λ' := lt_of_lt_of_le one_pos hΛ'
  have hD : 0 < C' * Λ' ^ M.G.homogeneousDimension := by positivity
  have hD' : 0 < C' * Λ ^ M.G.homogeneousDimension := by positivity
  refine ⟨rs, δf, cf / (C' * Λ' ^ M.G.homogeneousDimension),
    Cf * (C' * Λ ^ M.G.homogeneousDimension), hrs, hδf0, hδf1, div_pos hcf hD,
    mul_pos hCf hD', ?_⟩
  intro η hη r hr hrs'
  obtain ⟨hr1, hcl1, hrd1, hΛrd, hΛr0, hΛrr, hΛ'rr⟩ := hrad r hr hrs'
  dsimp only
  have hΛr : 0 < Λ * r := mul_pos hΛ0 hr
  have hrΛr : r ≤ Λ * r := by nlinarith
  have hδ'0 : 0 < r / Λ' := div_pos hr hΛ'0
  have hδ'r : r / Λ' ≤ r := div_le_self hr.le hΛ'
  refine ⟨?_, ?_⟩
  · -- upper bound
    intro z
    by_cases hz : z ∈ rsBall Ω w X (basePoint η) r
    · obtain ⟨-, -, -, hU0, hV0, -, hV0pos, -⟩ := hfacts η hη r hr hrd1
      obtain ⟨-, -, -, hU1, hV1, -, hV1pos, -⟩ := hfacts η hη (Λ * r) hΛr hΛrd
      obtain ⟨hup, -⟩ := hresc η hη Λ r hΛ hr hΛrr
      have hupR : fiberRescalingRatio Ω w X L.P η (Λ * r) ≤
          (C' * Λ ^ M.G.homogeneousDimension) * fiberRescalingRatio Ω w X L.P η r :=
        fiberRescaling_real_ratio_le hU1 hU0 hV1 hV0 hV1pos hV0pos hD'.le hup
      obtain ⟨hV, hU, -⟩ := hcmp η hη r hr hr1
      refine fiberRescaling_upper L hr hCw hCs hV hU
        (hS η hη (Λ * r) hΛr hΛr0) ?_ hz
      calc Cf * fiberRescalingRatio Ω w X L.P η (Λ * r)
          ≤ Cf * ((C' * Λ ^ M.G.homogeneousDimension) *
              fiberRescalingRatio Ω w X L.P η r) := mul_le_mul_of_nonneg_left hupR hCf.le
        _ = Cf * (C' * Λ ^ M.G.homogeneousDimension) *
              fiberRescalingRatio Ω w X L.P η r := by ring
    · exact (fiberVolume_triangularLift_eq_zero_outside hΩ w X L.P η r z hz).trans_le
        zero_le
  · -- lower bound
    intro z hz
    obtain ⟨-, -, -, hU0, hV0, -, hV0pos, -⟩ := hfacts η hη r hr hrd1
    obtain ⟨-, -, -, hU1, hV1, -, hV1pos, -⟩ := hfacts η hη (r / Λ') hδ'0 (hδ'r.trans_lt hrd1)
    obtain ⟨-, hlow⟩ := hresc η hη Λ' r hΛ' hr hΛ'rr
    have hlowR : (1 / (C' * Λ' ^ M.G.homogeneousDimension)) *
        fiberRescalingRatio Ω w X L.P η r ≤ fiberRescalingRatio Ω w X L.P η (r / Λ') :=
      fiberRescaling_real_ratio_ge hU1 hU0 hV1 hV0 hV1pos hV0pos (by positivity) hlow
    have hδr : δf * r ≤ r := by nlinarith
    obtain ⟨hV, -, -⟩ := hcmp η hη (δf * r) (mul_pos hδf0 hr) (hδr.trans hr1)
    have hclδ : cl * (r / Λ') ≤ r₁ := by
      have : cl * (r / Λ') ≤ cl * r := mul_le_mul_of_nonneg_left hδ'r hcl.le
      linarith
    obtain ⟨-, -, hL⟩ := hcmp η hη (cl * (r / Λ')) (mul_pos hcl hδ'0) hclδ
    have hCr : C * (cl * (r / Λ')) ≤ r := by
      have h1 : C * cl * (r / Λ') ≤ Λ' * (r / Λ') :=
        mul_le_mul_of_nonneg_right hCl (by positivity)
      have h2 : Λ' * (r / Λ') = r := by field_simp
      nlinarith
    have hL' : {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
        (triangularLift X L.P) η ξ < ENNReal.ofReal (cl * (r / Λ'))} ⊆
        rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r :=
      hL.trans (fiberRescaling_rsBall_mono _ _ _ _ hCr)
    have hδcw : C * (δf * r) ≤ cw * (r / Λ') := by
      have h1 : C * (δf * r) = (C * δf * Λ') * (r / Λ') := by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_right hδ (by positivity)
    refine fiberRescaling_lower L hδcw hV hL'
      (hS η hη (r / Λ') hδ'0 (hδ'r.trans (hrΛr.trans hΛr0))) ?_ hz
    calc cf / (C' * Λ' ^ M.G.homogeneousDimension) * fiberRescalingRatio Ω w X L.P η r
        = cf * ((1 / (C' * Λ' ^ M.G.homogeneousDimension)) *
            fiberRescalingRatio Ω w X L.P η r) := by ring
      _ ≤ cf * fiberRescalingRatio Ω w X L.P η (r / Λ') :=
          mul_le_mul_of_nonneg_left hlowR hcf.le

end RothschildStein.L1.CoordinateApproximationData
