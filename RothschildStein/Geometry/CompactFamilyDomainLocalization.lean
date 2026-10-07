-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.OrdinaryBallDomainLocalization
public import RothschildStein.G4.ContinuousShortFieldJets
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

/-- Compact external parameters give one first-exit radius for actual
ambient balls. Only joint continuity of the field values is needed. -/
theorem exists_compact_family_rsBall_domain_localization {P : Type*}
    [TopologicalSpace P] [CompactSpace P] {a n : ℕ}
    {Ω V K : Set (Fin n → ℝ)} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVΩ : V ⊆ Ω) (w : Fin a → ℕ+)
    (X : P → Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (fun q : P × (Fin n → ℝ) => X q.1 i q.2) (univ ×ˢ Ω)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ σ, ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
      rsBall Ω w (X σ) x r = rsBall V w (X σ) x r := by
  obtain ⟨R,hR,hRV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hc : ContinuousOn (fun q : P × (Fin n → ℝ) => ∑ i, ‖X q.1 i q.2‖)
      (univ ×ˢ cthickening R K) :=
    continuousOn_finsetSum _ (fun i _ => ((hX i).mono
      (fun q hq => ⟨hq.1,hVΩ (hRV hq.2)⟩)).norm)
  obtain ⟨B',hb⟩ := ((isCompact_univ.prod hK.cthickening).image_of_continuousOn hc).isBounded.exists_norm_le
  let B := max 1 B'
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hbuffer : ∀ x ∈ K, closedBall x R ⊆ V := by
    intro x hx z hz
    exact hRV (mem_cthickening_of_dist_le z x R K hx hz)
  have hbound : ∀ σ, ∀ x ∈ K, ∀ z, ‖z-x‖ ≤ R → ∑ i, ‖X σ i z‖ ≤ B := by
    intro σ x hx z hz
    have hh := hb _ (mem_image_of_mem _ (show (σ,z) ∈ univ ×ˢ cthickening R K from
      ⟨mem_univ _,mem_cthickening_of_dist_le z x R K hx (by simpa only [dist_eq_norm] using hz)⟩))
    exact (le_abs_self _).trans (hh.trans (le_max_right _ _))
  let ε := min 1 (R/(2*B))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hR (by positivity))
  refine ⟨ε,hε,?_⟩
  intro σ x hx r hr hrε
  ext y
  constructor
  · intro hy
    obtain ⟨δ,hδ,hδr,γ,hγ,hzero,hone⟩ :=
      G1.exists_controlledCurve_of_controlDistance_lt hy.2
    have hδ1 : δ ≤ 1 := hδr.le.trans (hrε.trans (min_le_left _ _))
    have hsmall : δ*B < R := by
      have hh := hδr.trans_le (hrε.trans (min_le_right _ _))
      have hm := (lt_div_iff₀ (by positivity : 0 < 2*B)).mp hh
      nlinarith
    have hmap : MapsTo γ (Icc 0 1) V := by
      intro t ht
      have hs := G4.controlledCurve_stays_ball hγ hδ1 hB.le hR hsmall
        (by simpa only [hzero] using hbound σ x hx) t ht
      exact hbuffer x hx (ball_subset_closedBall (by simpa only [hzero] using hs))
    have hv : isControlledCurve V w (X σ) δ γ :=
      ⟨hγ.1,hγ.2.1,hmap,hγ.2.2.2⟩
    have hc := G1.controlDistance_le_of_curve hv
    rw [hzero,hone] at hc
    refine ⟨by simpa only [hone] using hmap (by norm_num : (1 : ℝ) ∈ Icc 0 1), ?_⟩
    exact hc.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hδr)
  · intro hy
    exact ⟨hVΩ hy.1,(G1.controlDistance_mono_domain w (X σ) hVΩ x y).trans_lt hy.2⟩
end RothschildStein.Geometry
