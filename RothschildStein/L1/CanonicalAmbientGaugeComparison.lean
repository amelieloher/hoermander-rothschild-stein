-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalAmbientGaugeGeometry
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1

/-- The actual ambient gauge comparison in the single
constant and division format used by GaugeFiberData.gauge_comparison. -/
theorem exists_canonical_ambient_gauge_comparison {k s : ℕ} {p : Fin (k+1) → ℕ+}
    (D : G3.FreeModelData (k+1) s p) (hs : 1 ≤ s)
    (hw : ∀ i, (p i : ℕ) ≤ s)
    {U : Set (Fin (freeDimension (k+1) s p) → ℝ)} (hU : IsOpen U)
    (X : Fin (k+1) → (Fin (freeDimension (k+1) s p) → ℝ) →
      (Fin (freeDimension (k+1) s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) U)
    (hstep : bracketStepOn U p X s) (hFree : ∀ y ∈ U, FreeAt p s X y)
    {x : Fin (freeDimension (k+1) s p) → ℝ}
    (C : CanonicalFrameChartData U (canonicalWordFrame D X) x) :
    ∃ r Cρ : ℝ, 0 < r ∧ r ≤ C.radius ∧ 1 ≤ Cρ ∧
      ∀ Ω : Set (Fin (freeDimension (k+1) s p) → ℝ), U ⊆ Ω →
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
      ENNReal.ofReal (rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))/Cρ) ≤
        controlDistance Ω p X η ξ ∧
      controlDistance Ω p X η ξ ≤ ENNReal.ofReal
        (Cρ*rsGauge D.group.weight D.group.weight_pos (C.theta (η,ξ))) := by
  obtain ⟨r,A,B,_T,hr,hrC,_hA,_hB,_hT,he,_htri⟩ :=
    exists_canonical_ambient_gauge_geometry D hs hw hU X hX hstep hFree C
  let Cρ := max 1 (max A B)
  have hC1 : 1 ≤ Cρ := le_max_left _ _
  have hC : 0 < Cρ := zero_lt_one.trans_le hC1
  have hAC : A ≤ Cρ := (le_max_left A B).trans (le_max_right _ _)
  have hBC : B ≤ Cρ := (le_max_right A B).trans (le_max_right _ _)
  refine ⟨r,Cρ,hr,hrC,hC1,?_⟩
  intro Ω hUU η hη ξ hξ
  have hh := he Ω hUU η hη ξ hξ
  have hρ := G2.gauge_nonneg D.group (C.theta (η,ξ))
  constructor
  · rw [ENNReal.ofReal_div_of_pos hC]
    apply (ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top).mpr
    exact hh.2.2.2.trans (by gcongr)
  · exact hh.2.2.1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAC hρ))
end RothschildStein.L1
