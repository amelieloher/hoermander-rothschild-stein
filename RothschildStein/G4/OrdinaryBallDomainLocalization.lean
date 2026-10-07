-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.CompactPatchControlBalls
public import RothschildStein.G4.FirstExit
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal BigOperators
namespace RothschildStein.G4

/-- Small original control balls agree with the balls of any
open interior buffer, uniformly over compact centers. First exit retains
whole connecting curves, so endpoint containment alone is not used
(BB Theorem 9.1, p. 400; local-domain convention, p. 406). -/
theorem exists_uniform_rsBall_domain_localization {a n : ℕ}
    {Ω V K : Set (Fin n → ℝ)} (hK : IsCompact K) (hV : IsOpen V)
    (hKV : K ⊆ V) (hVΩ : V ⊆ Ω) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
      rsBall Ω w X x r = rsBall V w X x r := by
  obtain ⟨B,R,hB,hR,hbuffer,hbound⟩ :=
    G1.exists_uniform_control_buffer hK hV hKV hVΩ X hX
  let ε := min 1 (R/(2*B))
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hR (by positivity))
  refine ⟨ε,hε,?_⟩
  intro x hx r hr hrε
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
      have hs := controlledCurve_stays_ball hγ hδ1 hB.le hR hsmall
        (by simpa only [hzero] using hbound x hx) t ht
      exact hbuffer x hx (ball_subset_closedBall (by simpa only [hzero] using hs))
    have hv : isControlledCurve V w X δ γ :=
      ⟨hγ.1,hγ.2.1,hmap,hγ.2.2.2⟩
    have hc := G1.controlDistance_le_of_curve hv
    rw [hzero,hone] at hc
    refine ⟨by simpa only [hone] using hmap (by norm_num : (1 : ℝ) ∈ Icc 0 1), ?_⟩
    exact hc.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hδr)
  · intro hy
    exact ⟨hVΩ hy.1,(G1.controlDistance_mono_domain w X hVΩ x y).trans_lt hy.2⟩
end RothschildStein.G4
