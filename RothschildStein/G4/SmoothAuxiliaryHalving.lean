-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothAuxiliaryPrimitiveApproximation
public import RothschildStein.G4.SpanningLocalControlUpper
public import RothschildStein.G4.GeometricResidualEstimate
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- Actual primitive approximation and the spanning short-field estimate
produce a uniformly halving auxiliary residual inside a fixed buffer. -/
theorem exists_smooth_auxiliary_halving {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (D : FreeModelData (k+1) s w) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C η M : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧
      0 < C ∧ 0 < η ∧ 0 < M ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        ∃ p ∈ closedBall z R,
          controlDistance Ω w X x p ≤ ENNReal.ofReal (C*δ) ∧
          auxiliaryDistance (s := s) Ω w X p y ≤ ENNReal.ofReal (δ/4) ∧
          ‖p-y‖ ≤ M*δ^(s+1) := by
  obtain ⟨R₁, C, η₁, M, hR₁, hR₁Ω, hC, hη₁, hM, ha⟩ :=
    exists_smooth_auxiliary_primitive_approximation hn hs w D hw hΩ X hX hstep hz
  obtain ⟨R₂, L, hR₂, hL, hR₂Ω, hu⟩ :=
    exists_auxiliary_local_control_upper (by omega) hΩ w X hX hstep hz
  let R := min (R₁/16) R₂
  have hR : 0 < R := lt_min (by positivity) hR₂
  have hRR₁ : R ≤ R₁/16 := min_le_left _ _
  have hRR₂ : R ≤ R₂ := min_le_right _ _
  let η := min η₁ (min 1 (min (R/(2*M)) ((1/4 : ℝ)^s/(L*M))))
  have hη : 0 < η := lt_min hη₁ (lt_min zero_lt_one
    (lt_min (div_pos hR (by positivity)) (div_pos (by positivity) (mul_pos hL hM))))
  refine ⟨R, C, η, M, hR,
    (closedBall_subset_closedBall hRR₂).trans hR₂Ω, hC, hη, hM, ?_⟩
  intro x hx y hy δ hδ hδη hd
  have hδ₁ : δ < η₁ := hδη.trans_le (min_le_left _ _)
  have hδrest : δ < min 1 (min (R/(2*M)) ((1/4 : ℝ)^s/(L*M))) :=
    hδη.trans_le (min_le_right _ _)
  have hδone : δ ≤ 1 := hδrest.le.trans (min_le_left _ _)
  have hδtail : δ < min (R/(2*M)) ((1/4 : ℝ)^s/(L*M)) :=
    hδrest.trans_le (min_le_right _ _)
  have hδR : M*δ < R/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*M)).mp
      (hδtail.trans_le (min_le_left _ _))
    nlinarith
  have hsmall : (L*M)*δ ≤ (1/4 : ℝ)^s := by
    have hh := (lt_div_iff₀ (mul_pos hL hM)).mp
      (hδtail.trans_le (min_le_right _ _))
    nlinarith
  have hpow : δ^(s+1) ≤ δ := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ hδ.le hδone) hδ.le
  obtain ⟨p, _hpΩ, hcost, herr⟩ := ha x
    (closedBall_subset_closedBall hRR₁ hx) δ hδ hδ₁ y hd
  have hpR : p ∈ closedBall z R := by
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    have hh := norm_sub_le_norm_sub_add_norm_sub p y z
    have he := herr.trans (mul_le_mul_of_nonneg_left hpow hM.le)
    linarith
  have herror : L*‖y-p‖ ≤ (L*M)*δ^(s+1) := by
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left herr hL.le).trans_eq (by ring)
  have hunit : L*‖y-p‖ ≤ 1 := by
    have hh : (1/4 : ℝ)^s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact herror.trans ((mul_le_mul_of_nonneg_left hpow (mul_pos hL hM).le).trans
      (hsmall.trans hh))
  have hu' := hu p (closedBall_subset_closedBall hRR₂ hpR) y
    (closedBall_subset_closedBall hRR₂ (closedBall_subset_closedBall (by linarith) hy)) hunit
  refine ⟨p, hpR, hcost, hu'.trans (ENNReal.ofReal_le_ofReal ?_), herr⟩
  exact (Real.rpow_le_rpow (by positivity) herror (by positivity)).trans
    (geometric_residual_rpow_le_quarter (by omega) (mul_pos hL hM).le hδ.le hsmall)
end RothschildStein.G4
