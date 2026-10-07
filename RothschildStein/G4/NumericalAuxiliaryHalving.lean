-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalAuxiliaryPrimitiveApproximation
public import RothschildStein.G4.NumericalAuxiliaryLocalControlUpper
public import RothschildStein.G4.GeometricResidualEstimate
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- Numerical primitive corrections and numerical Cramer bounds give a
uniformly halving auxiliary residual. -/
theorem exists_numerical_auxiliary_halving (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (D : G3.FreeModelData (k+1) s w)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R₀ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR₀ : 0 < R₀) :
    ∃ R C η E : ℝ, 0 < R ∧ 0 < C ∧ 0 < η ∧ 0 < E ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R₀ ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R₀) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R₀, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ closedBall x₀ R,
          controlDistance Ω w X x p ≤ ENNReal.ofReal (C*δ) ∧
          auxiliaryDistance (s := s) Ω w X p y ≤ ENNReal.ofReal (δ/4) ∧
          ‖p-y‖ ≤ E*δ^(s+1) := by
  obtain ⟨C,η₁,E,hC,hη₁,hE,ha⟩ :=
    exists_numerical_auxiliary_primitive_approximation k n s h q hn hs horder hq w D hw M Δ R₀ hM hΔ hR₀
  obtain ⟨R₂,L,hR₂,_hR₂R,hL,hup⟩ :=
    exists_numerical_auxiliary_local_control_upper hs w M Δ R₀ hM hΔ hR₀
  let R := min (R₀/16) R₂
  have hR : 0 < R := lt_min (by positivity) hR₂
  have hRR₀ : R ≤ R₀/16 := min_le_left _ _
  have hRR₂ : R ≤ R₂ := min_le_right _ _
  let η := min η₁ (min 1 (min (R/(2*E)) ((1/4 : ℝ)^s/(L*E))))
  have hη : 0 < η := lt_min hη₁ (lt_min zero_lt_one
    (lt_min (div_pos hR (by positivity)) (div_pos (by positivity) (mul_pos hL hE))))
  refine ⟨R,C,η,E,hR,hC,hη,hE,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  have hap := ha Ω hΩ X hX hstep z hRΩ hjets hmax
  obtain ⟨hR₂Ω,hu⟩ := hup Ω hΩ X hX z hRΩ
    (fun i => (hjets i).mono ((le_max_right _ _).trans (le_max_right _ _)))
    (hmax z (mem_closedBall_self hR₀.le))
  refine ⟨(closedBall_subset_closedBall hRR₂).trans hR₂Ω,?_⟩
  intro x hx y hy δ hδ hδη hd
  have hδ₁ : δ < η₁ := hδη.trans_le (min_le_left _ _)
  have hδrest : δ < min 1 (min (R/(2*E)) ((1/4 : ℝ)^s/(L*E))) :=
    hδη.trans_le (min_le_right _ _)
  have hδone : δ ≤ 1 := hδrest.le.trans (min_le_left _ _)
  have hδtail : δ < min (R/(2*E)) ((1/4 : ℝ)^s/(L*E)) :=
    hδrest.trans_le (min_le_right _ _)
  have hδR : E*δ < R/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*E)).mp
      (hδtail.trans_le (min_le_left _ _))
    nlinarith
  have hsmall : (L*E)*δ ≤ (1/4 : ℝ)^s := by
    have hh := (lt_div_iff₀ (mul_pos hL hE)).mp
      (hδtail.trans_le (min_le_right _ _))
    nlinarith
  have hpow : δ^(s+1) ≤ δ := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ hδ.le hδone) hδ.le
  obtain ⟨p, _hpΩ, hcost, herr⟩ := hap x
    (closedBall_subset_closedBall hRR₀ hx) δ hδ hδ₁ y hd
  have hpR : p ∈ closedBall z R := by
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    have hh := norm_sub_le_norm_sub_add_norm_sub p y z
    have he := herr.trans (mul_le_mul_of_nonneg_left hpow hE.le)
    linarith
  have herror : L*‖y-p‖ ≤ (L*E)*δ^(s+1) := by
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left herr hL.le).trans_eq (by ring)
  have hunit : L*‖y-p‖ ≤ 1 := by
    have hh : (1/4 : ℝ)^s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact herror.trans ((mul_le_mul_of_nonneg_left hpow (mul_pos hL hE).le).trans
      (hsmall.trans hh))
  have hu' := hu p (closedBall_subset_closedBall hRR₂ hpR) y
    (closedBall_subset_closedBall hRR₂ (closedBall_subset_closedBall (by linarith) hy)) hunit
  refine ⟨p, hpR, hcost, hu'.trans (ENNReal.ofReal_le_ofReal ?_), herr⟩
  exact (Real.rpow_le_rpow (by positivity) herror (by positivity)).trans
    (geometric_residual_rpow_le_quarter (by omega) (mul_pos hL hE).le hδ.le hsmall)
end RothschildStein.G4
