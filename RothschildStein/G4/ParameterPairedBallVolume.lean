-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.ParameterAuxiliaryBallVolume
public import RothschildStein.G4.NumericalUniformDistanceComparisons
public import RothschildStein.G4.NumericalDistanceBallSandwich
public import RothschildStein.G4.OrdinaryBallVolumeTransfer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- The same constants bound both actual balls uniformly
across the compact external family on a spatial buffer (BB p. 405). -/
theorem exists_parameter_paired_ball_volume_bounds {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Sg → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ j, ContDiffOn ℝ (⊤ : ℕ∞) (X σ j) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ J, ∀ i ≤ s+1, ContinuousOn
      (fun z : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2) (univ ×ˢ Ω))
    (x₀ : Fin n → ℝ) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hjets : ∀ σ j, HasJetBound Ω (closedBall x₀ R) (X σ j)
      (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
        (max (4*(s+1)^3) (1+s))) M)
    (hmax : ∀ σ, ∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
      Δ ≤ |frameDet (shortField w (X σ)) B y|)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKball : K ⊆ ball x₀ (R/8)) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf := fun σ j => shortField w (X σ) (shortIndex (s := s) w j)
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
        let Λ := volumePolynomial (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
          (fun B => ∑ i, (wf (B i) : ℕ)) r
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω w (X σ) x r) ∧
          volume (controlBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C*Λ)) ∧
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω wf (Zf σ) x r) ∧
          volume (controlBall Ω wf (Zf σ) x r) ≤ ENNReal.ofReal (C*Λ)) := by
  intro m wf Zf
  obtain ⟨c₀,C₀,ε₀,hc₀,hC₀,hε₀,haux⟩ :=
    exists_parameter_auxiliary_ball_volume_bounds k n s h q hn hs horder hq w M Δ R
      hM hΔ hR Ω hΩ X hX hstep hjoint x₀ hRΩ
      (fun σ j => (hjets σ j).mono (le_max_left _ _)) hmax K hK hKball
  obtain ⟨Ceq,_Cbox,εeq,hCeq,_hCbox,hεeq,hcomp⟩ :=
    exists_numerical_uniform_distance_comparisons k n s h q hn hs horder hq w hw
      M Δ (R/2) hM hΔ (half_pos hR)
  let A := max 1 (2*Ceq)
  have hA : 1 ≤ A := le_max_left _ _
  have hAp : 0 < A := zero_lt_one.trans_le hA
  let c := min c₀ (c₀/A^(n*s))
  have hc : 0 < c := lt_min hc₀ (div_pos hc₀ (pow_pos hAp _))
  refine ⟨c,C₀,min ε₀ (εeq/2),hc,hC₀,lt_min hε₀ (half_pos hεeq),?_⟩
  intro σ x hx r hr hrr
  have hxr : x ∈ ball x₀ (R/8) := hKball hx
  have hbuffer : closedBall x (R/2) ⊆ closedBall x₀ R := by
    intro y hy
    rw [mem_closedBall] at hy ⊢
    rw [mem_ball] at hxr
    have hh := dist_triangle y x x₀
    linarith
  have hhcomp := hcomp Ω hΩ (X σ) (hX σ) (hstep σ) x (hbuffer.trans hRΩ)
    (fun j a ha y hy => hjets σ j a ha y (hbuffer hy))
    (fun y hy => hmax σ y (hbuffer hy))
  have hweight : ∀ B : Fin n → Fin m, (∑ i, (wf (B i) : ℕ)) ≤ n*s :=
    frame_natural_weight_le wf
      (fun j => ((mem_shortWordFamily_iff w (shortIndex w j).val).mp (shortIndex w j).property).2)
  have hr₀ : r ≤ ε₀ := hrr.trans (min_le_left _ _)
  have hballs := ordinary_auxiliary_ball_sandwich_of_distance_bound Ω w (X σ) hw x hCeq hA
    (le_max_right _ _) hr ((hrr.trans (min_le_right _ _)).trans_lt (half_lt_self hεeq))
    (fun y hy => (hhcomp y hy).2.1)
  have hvol := ordinary_ball_volume_bounds_of_ball_sandwich volume
    (fun t => controlBall Ω wf (Zf σ) x t) (fun t => controlBall Ω w (X σ) x t)
    (fun B => frameDet (Zf σ) B x) (fun B => ∑ i, (wf (B i) : ℕ)) hweight hA hc₀ hr hr₀
    (haux σ x hx) hballs
  have hΛ := volumePolynomial_nonneg (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
    (fun B => ∑ i, (wf (B i) : ℕ)) hr.le
  have ha := haux σ x hx r hr hr₀
  refine ⟨⟨?_,hvol.2⟩,⟨?_,ha.2⟩⟩
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right _ _) hΛ)).trans hvol.1
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) hΛ)).trans ha.1
end RothschildStein.G4
