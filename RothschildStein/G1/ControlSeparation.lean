-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledDisplacement
public import RothschildStein.G1.WeightedTriangle
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators ENNReal

namespace RothschildStein.G1

/-- The first-exit estimate gives the non-strict lower bound R/B for the
control parameter needed for a curve to reach radius R (BB pp. 19, 23). -/
theorem controlledCurve_firstExit_bound {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ B R : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ)
    (hδ1 : δ ≤ 1) (hB : 0 ≤ B) (hR : 0 < R)
    (hend : R ≤ ‖γ 1 - γ 0‖)
    (hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) : R ≤ δ * B := by
  have hf : ContinuousOn (fun t => ‖γ t - γ 0‖) (Icc 0 1) := by
    simpa only [uIcc_of_le zero_le_one, Pi.sub_apply] using (hγ.2.1.continuousOn.sub continuousOn_const).norm
  have hex : ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t - γ 0‖ = R :=
    intermediate_value_Icc zero_le_one hf ⟨by simpa using hR.le, hend⟩
  let S : Set ℝ := Icc 0 1 ∩ (fun t => ‖γ t - γ 0‖) ⁻¹' {R}
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  obtain ⟨b, hb, hmin⟩ := (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isMinOn
    (by obtain ⟨t, ht, he⟩ := hex; exact ⟨t, ht, he⟩) continuousOn_id
  have hbefore : ∀ t ∈ Icc 0 b, ‖γ t - γ 0‖ ≤ R := by
    intro t ht
    by_cases htb : t = b
    · subst t; exact hb.2.le
    · by_contra hbad
      have ht1 : t ≤ 1 := ht.2.trans hb.1.2
      obtain ⟨v, hv, he⟩ := intermediate_value_Icc ht.1
        (hf.mono (Icc_subset_Icc le_rfl ht1))
        (show R ∈ Icc ‖γ 0 - γ 0‖ ‖γ t - γ 0‖ from ⟨by simpa using hR.le, le_of_not_ge hbad⟩)
      have hbl : b ≤ v := hmin ⟨⟨hv.1, hv.2.trans ht1⟩, he⟩
      have hlt : t < b := lt_of_le_of_ne ht.2 htb
      linarith [hv.2]
  have hm := controlledCurve_initial_displacement_le hγ hδ1 hB hb.1
    (fun t ht => hbound (γ t) (hbefore t ht))
  have hmul : δ * B * b ≤ δ * B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.1.2 (mul_nonneg hγ.1.le hB)
  exact hb.2.symm.le.trans (hm.trans hmul)

/-- A local bounded-field buffer separates distinct endpoints in the
extended control distance; no rank assumption is used (BB pp. 19, 23). -/
theorem controlDistance_ne_zero_of_local_bound {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {x y : Fin n → ℝ} {B R : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hxy : R ≤ ‖y - x‖) (hbound : ∀ z, ‖z - x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B) :
    controlDistance Ω w X x y ≠ 0 := by
  intro hzero
  have hr : 0 < min 1 (R / B) := lt_min zero_lt_one (div_pos hR hB)
  obtain ⟨δ, hδ, hδr, γ, hγ, hγ0, hγ1⟩ :=
    exists_controlledCurve_of_controlDistance_lt
      (show controlDistance Ω w X x y < ENNReal.ofReal (min 1 (R / B)) by
        rw [hzero]; exact ENNReal.ofReal_pos.mpr hr)
  have hm := controlledCurve_firstExit_bound hγ (hδr.trans_le (min_le_left _ _)).le hB.le hR
    (by simpa only [hγ0, hγ1] using hxy) (by simpa only [hγ0] using hbound)
  have hsmall := (lt_div_iff₀ hB).mp (hδr.trans_le (min_le_right _ _))
  linarith

/-- Smooth fields on an open domain give separation, before bracket rank
or connectivity is assumed (BB Prop 1.41, pp. 22–23). -/
theorem controlDistance_eq_zero_iff {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) {x y : Fin n → ℝ} (hx : x ∈ Ω) :
    controlDistance Ω w X x y = 0 ↔ x = y := by
  refine ⟨?_, fun h => by subst y; exact controlDistance_self w X hx⟩
  intro hd
  by_contra hxy
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let R := min (a / 2) (‖y - x‖ / 2)
  have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hKΩ : closedBall x R ⊆ Ω := by
    intro z hz
    apply hball
    have hzR : dist z x ≤ R := hz
    have hRa : R < a := (min_le_left _ _).trans_lt (by linarith)
    exact hzR.trans_lt hRa
  have hc : ContinuousOn (fun z => ∑ i, ‖X i z‖) (closedBall x R) :=
    continuousOn_finsetSum _ (fun i _ => ((hX i).mono hKΩ).norm)
  obtain ⟨B, hbound⟩ := ((isCompact_closedBall x R).image_of_continuousOn hc).isBounded.exists_norm_le
  have hB : 0 < max 1 B := zero_lt_one.trans_le (le_max_left _ _)
  apply controlDistance_ne_zero_of_local_bound hB hR
    ((min_le_right _ _).trans (by linarith : ‖y - x‖ / 2 ≤ ‖y - x‖)) (x := x) (y := y) (Ω := Ω) (w := w) (X := X) _ hd
  intro z hz
  have hnormB := hbound _ (mem_image_of_mem _ (show z ∈ closedBall x R from by
    simpa only [mem_closedBall, dist_eq_norm] using hz))
  exact (le_abs_self _).trans (hnormB.trans (le_max_right _ _))

end RothschildStein.G1
