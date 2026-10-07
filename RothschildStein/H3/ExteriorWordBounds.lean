-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExteriorWordHomogeneity
public import RothschildStein.H3.CutoffPlateauJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.H3
variable {N m : ℕ} {G : HomogeneousGroup N}

/-- far part. Every fixed homogeneous word of the unit
exterior kernel has a finite global bound when its degree is nonpositive.
Near zero the kernel is smooth; at infinity the homogeneous tail controls it. -/
theorem exteriorCutoffKernel_word_unit_bound (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hsY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hhY : ∀ i, G2.IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ))
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hzero : ∀ t : ℝ, 1 ≤ t → φ t = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    (I : List (Fin m)) (hdegree : γ - (wordWeight w I : ℝ) ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |wordDerivative Y I (exteriorCutoffKernel ν φ F 1) x| ≤ C := by
  have hc := contDiff_kernel_exterior_cutoff hν hsν hφ hone hF zero_lt_one
  have hp : Continuous (wordDerivative Y I (exteriorCutoffKernel ν φ F 1)) :=
    (contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Y
      (fun i => (hsY i).contDiffOn) I _ hc.contDiffOn)).continuous
  obtain ⟨M, hM⟩ := (G2.isCompact_gauge_le hν 2).bddAbove_image hp.norm.continuousOn
  obtain ⟨hWF, hwhom⟩ := homogeneous_word_kernel w Y hsY hhY hF hhom I
  obtain ⟨B, _, htail⟩ := homogeneous_function_exterior_bound hν hdegree hWF.continuousOn hwhom
  refine ⟨max 0 (max M B), le_max_left _ _, ?_⟩
  intro x
  by_cases hx : ν x ≤ 2
  · have hb := hM ⟨x, hx, rfl⟩
    change ‖wordDerivative Y I (exteriorCutoffKernel ν φ F 1) x‖ ≤ M at hb
    rw [Real.norm_eq_abs] at hb
    exact hb.trans ((le_max_left M B).trans (le_max_right 0 _))
  · have he : exteriorCutoffKernel ν φ F 1 =ᶠ[𝓝 x] F := by
      have hx1 : 1 < ν x := by linarith [lt_of_not_ge hx]
      filter_upwards [hν.1.continuousAt.eventually (lt_mem_nhds hx1)] with y hy
      unfold exteriorCutoffKernel
      rw [div_one, hzero _ hy.le, sub_zero, one_mul]
    rw [(wordDerivative_eventuallyEq Y I he).eq_of_nhds]
    have hb := htail 1 zero_lt_one x (by linarith [lt_of_not_ge hx])
    simp only [Real.one_rpow, mul_one] at hb
    exact hb.trans ((le_max_right M B).trans (le_max_right 0 _))

/-- far part. The fixed mixed-word global bound has exactly
scale epsilon^(kernel degree minus word weight), uniformly in epsilon.
This supplies the weights two, three and four used on BB p. 383. -/
theorem exteriorCutoffKernel_word_bound (w : Fin m → ℕ+)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hsY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i))
    (hhY : ∀ i, G2.IsHomogeneousField G (Y i) ((w i : ℕ) : ℝ))
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hzero : ∀ t : ℝ, 1 ≤ t → φ t = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x)
    (I : List (Fin m)) (hdegree : γ - (wordWeight w I : ℝ) ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ x,
      |wordDerivative Y I (exteriorCutoffKernel ν φ F ε) x| ≤
        C * ε ^ (γ - (wordWeight w I : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exteriorCutoffKernel_word_unit_bound w Y hsY hhY
    hν hsν hφ hone hzero hF hhom I hdegree
  refine ⟨C, hC, ?_⟩
  intro ε hε x
  rw [exteriorCutoffKernel_word_scale w Y hsY hhY hν hsν hφ hone hF hhom I hε,
    abs_mul, abs_of_pos (Real.rpow_pos_of_pos hε _)]
  exact (mul_le_mul_of_nonneg_left (hb _) (Real.rpow_nonneg hε.le _)).trans_eq (mul_comm _ _)

end RothschildStein.H3
