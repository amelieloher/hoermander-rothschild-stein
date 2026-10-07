-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.PicardFlowBuffer
public import RothschildStein.G4.FixedBufferLipschitz
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped NNReal

namespace RothschildStein.G4

/-- A prescribed field-value bound on a fixed buffer gives a
jointly smooth flow for the full time-one interval and its neighborhood.
The auxiliary Lipschitz constant does not shrink this interval. -/
theorem exists_smooth_fixed_time_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [ProperSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (x₀ : E) {R : ℝ} (hR : 0 < R)
    (hRΩ : closedBall x₀ R ⊆ Ω) (hbound : ∀ x ∈ closedBall x₀ R, ‖Z x‖ ≤ R / 16) :
    ∃ Φ : E × ℝ → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ (ball x₀ (R / 4) ×ˢ Ioo (-2) 2) ∧
      ∀ x ∈ ball x₀ (R / 4), Φ (x, 0) = x ∧
        ∀ t ∈ Ioo (-2) 2, Φ (x, t) ∈ closedBall x₀ R ∧
          HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  obtain ⟨K, hLip⟩ := exists_lipschitzOnWith_on_fixed_buffer hΩ hZ x₀ R hRΩ
  let a := Real.toNNReal R
  let r := Real.toNNReal (R / 4)
  let L := Real.toNNReal (R / 16)
  have ha : (a : ℝ) = R := Real.coe_toNNReal _ hR.le
  have hr : (r : ℝ) = R / 4 := Real.coe_toNNReal _ (by positivity)
  have hL : (L : ℝ) = R / 16 := Real.coe_toNNReal _ (by positivity)
  have hpl : IsPicardLindelof (fun _ : ℝ => Z) (tmin := -2) (tmax := 2)
      ⟨0, by constructor <;> norm_num⟩ x₀ a r L K := by
    constructor
    · intro t ht
      simpa only [ha] using hLip
    · intro x hx
      exact continuousOn_const
    · intro t ht x hx
      simpa only [hL] using hbound x (by simpa only [ha] using hx)
    · change (L : ℝ) * max (2 - 0) (0 - (-2)) ≤ (a : ℝ) - (r : ℝ)
      rw [ha, hr, hL]
      norm_num
      linarith
  obtain ⟨Φ, hc, hsol⟩ := exists_picard_flow_with_buffer hpl
  have hinner : ball x₀ (R / 4) ⊆ closedBall x₀ (r : ℝ) := by
    rw [hr]
    exact ball_subset_closedBall
  have hsol' : ∀ x ∈ ball x₀ (R / 4), Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-2) 2,
      Φ (x, t) ∈ closedBall x₀ R ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
    intro x hx
    refine ⟨(hsol x (hinner hx)).1, ?_⟩
    intro t ht
    have hb := (hsol x (hinner hx)).2 t ⟨ht.1.le, ht.2.le⟩
    exact ⟨by simpa only [ha] using hb.1, hb.2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  have hs := G1.local_flow_contDiffOn hΩ isOpen_ball (by norm_num : (0 : ℝ) < 2) hZ
    (hc.mono (prod_mono hinner Ioo_subset_Icc_self))
    (fun x hx => (hsol' x hx).1)
    (fun x hx t ht => ⟨hRΩ ((hsol' x hx).2 t ht).1, ((hsol' x hx).2 t ht).2⟩)
  exact ⟨Φ, hs, hsol'⟩

end RothschildStein.G4
