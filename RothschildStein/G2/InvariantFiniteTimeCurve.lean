-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantFlowParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Positive dilations and time rescaling extend a local integral curve of a left-invariant field through the identity to any finite interval (BB Proposition 3.42(a), pp. 117–118). -/
theorem exists_leftField_curve_on_interval (v : Fin N → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ γ : ℝ → (Fin N → ℝ), γ 0 = 0 ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt γ (leftField G v (γ t)) t := by
  obtain ⟨r,hr,τ,hτ,Φ,_hball,_hc,hODE⟩ := G1.exists_continuous_parameter_flow
    (A := univ) (Ω := univ) isOpen_univ isOpen_univ
    (fun q : (Fin N → ℝ) × (Fin N → ℝ) => leftField G q.1 q.2)
    (contDiff_leftField_parameters G).contDiffOn
    (show (0 : Fin N → ℝ) ∈ univ from mem_univ _)
    (show (0 : Fin N → ℝ) ∈ univ from mem_univ _)
  let a : ℝ := τ/(2*T)
  have ha : 0 < a := div_pos hτ (by positivity)
  obtain ⟨l,hl,hsmall⟩ := exists_small_dilated_parameter G v (c := a⁻¹) hr
  let w := a⁻¹ • G.dilate l v
  have hp : (w,(0 : Fin N → ℝ)) ∈ ball (0,0) r := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by simpa only [dist_zero_right,w] using hsmall,by simpa using hr⟩
  let γ := fun t : ℝ => G.dilate l⁻¹ (Φ ((w,0),a*t))
  have hrecover : a • G.dilate l⁻¹ w = v := by
    dsimp only [w]
    rw [dilate_smul,smul_smul,mul_inv_cancel₀ ha.ne',one_smul,dilate_inv_dilate G hl.ne']
  refine ⟨γ,?_,?_⟩
  · change G.dilate l⁻¹ (Φ ((w,0),a*0)) = 0
    rw [show a*0 = 0 by ring,(hODE (w,0) hp).1,dilate_zero]
  · intro t ht
    have htime : a*t ∈ Ioo (-τ) τ := by
      have hbound : a*T = τ/2 := by dsimp [a]; field_simp
      have h₁ := mul_lt_mul_of_pos_left ht.1 ha
      have h₂ := mul_lt_mul_of_pos_left ht.2 ha
      constructor <;> nlinarith only [h₁,h₂,hbound,hτ]
    have hd := ((hODE (w,0) hp).2 (a*t) htime).2
    have hdt := hd.scomp t ((hasDerivAt_id t).const_mul a)
    have hh := (hasFDerivAt_dilate G l⁻¹ (Φ ((w,0),a*t))).comp_hasDerivAt t hdt
    have he : G.dilate l⁻¹ (a • leftField G w (Φ ((w,0),a*t))) =
        leftField G v (γ t) := by
      rw [dilate_smul,dilate_leftField G l⁻¹ (inv_pos.mpr hl)]
      change a • fderiv ℝ (G.mul (γ t)) 0 (G.dilate l⁻¹ w) = _
      rw [← map_smul,hrecover]
      rfl
    change HasDerivAt γ (G.dilate l⁻¹ ((a*1) • leftField G w (Φ ((w,0),a*t)))) t at hh
    simpa only [mul_one,he] using hh

end RothschildStein.G2
