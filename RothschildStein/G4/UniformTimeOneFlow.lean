-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FixedTimeParameterFlow
public import RothschildStein.G4.TimeOneFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- A common field-value budget gives an explicit coefficient
radius for a smooth time-one flow on the prescribed spatial buffer. -/
theorem exists_uniform_timeOne_flow {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (x₀ : Fin n → ℝ) {R A : ℝ} (hR : 0 < R) (hA : 0 ≤ A)
    (hRΩ : closedBall x₀ R ⊆ Ω)
    (hbound : ∀ x ∈ closedBall x₀ R, ∑ j, ‖Z j x‖ ≤ A) :
    ∃ Ψ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ
        ((ball 0 (R / (64 * (1 + A))) ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
      ∀ a ∈ ball 0 (R / (64 * (1 + A))), ∀ x ∈ ball x₀ (R / 4),
        Ψ ((a, x), 0) = x ∧ ∀ t ∈ Ioo (-2) 2,
          Ψ ((a, x), t) ∈ closedBall x₀ R ∧
            HasDerivAt (fun v => Ψ ((a, x), v))
              (∑ j, a j • Z j (Ψ ((a, x), t))) t := by
  let θ : ℝ := 1 / (16 * (1 + A))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let T := fun p => θ • constantCombination Z p
  have hT : ContDiffOn ℝ (⊤ : ℕ∞) T (univ ×ˢ Ω) :=
    (contDiffOn_const (c := θ)).smul (constantCombination_contDiffOn hZ)
  have hb : ∀ p ∈ closedBall ((0 : Fin m → ℝ), x₀) R, ‖T p‖ ≤ R / 16 := by
    intro p hp
    have hdist := mem_closedBall.mp hp
    rw [Prod.dist_eq, dist_zero_right] at hdist
    have hx : p.2 ∈ closedBall x₀ R := (le_max_right _ _).trans hdist
    have ha : ‖p.1‖ ≤ R := (le_max_left _ _).trans hdist
    have hi : ∀ j, |p.1 j| ≤ R := fun j => (norm_le_pi_norm p.1 j).trans ha
    have hc : ‖constantCombination Z p‖ ≤ R * A := by
      apply (norm_sum_le _ _).trans
      calc
        ∑ j, ‖p.1 j • Z j p.2‖ ≤ ∑ j, R * ‖Z j p.2‖ := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hi j) (norm_nonneg _)
        _ = R * ∑ j, ‖Z j p.2‖ := (Finset.mul_sum _ _ _).symm
        _ ≤ R * A := mul_le_mul_of_nonneg_left (hbound p.2 hx) hR.le
    change ‖θ • constantCombination Z p‖ ≤ R / 16
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
    apply (mul_le_mul_of_nonneg_left hc hθ.le).trans
    dsimp [θ]
    have hden : 0 < 16 * (1 + A) := by positivity
    rw [one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  obtain ⟨Φ, hs, hΦ⟩ := exists_smooth_fixed_time_parameter_flow hΩ T hT x₀ hR hRΩ hb
  let S : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) →
      (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
    fun pt => ((θ⁻¹ • pt.1.1, pt.1.2), pt.2)
  have hS : ContDiff ℝ (⊤ : ℕ∞) S :=
    (((contDiff_const (c := θ⁻¹)).smul contDiff_fst.fst).prodMk
      contDiff_fst.snd).prodMk contDiff_snd
  have hmap : MapsTo S
      ((ball 0 (R / (64 * (1 + A))) ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2)
      (ball ((0 : Fin m → ℝ), x₀) (R / 4) ×ˢ Ioo (-2) 2) := by
    intro pt hpt
    refine ⟨?_, hpt.2⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, hpt.1.2⟩
    change dist (θ⁻¹ • pt.1.1) 0 < R / 4
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ)]
    apply (inv_mul_lt_iff₀ hθ).mpr
    have ha := mem_ball.mp hpt.1.1
    rw [dist_zero_right] at ha
    convert ha using 1
    dsimp [θ]
    field_simp
    ring
  refine ⟨(fun pt => Φ (S pt)), hs.comp hS.contDiffOn hmap, ?_⟩
  intro a ha x hx
  have hp : (θ⁻¹ • a, x) ∈ ball ((0 : Fin m → ℝ), x₀) (R / 4) :=
    (hmap (show ((a, x), (0 : ℝ)) ∈ _ from ⟨⟨ha, hx⟩, by constructor <;> norm_num⟩)).1
  refine ⟨(hΦ _ hp).1, ?_⟩
  intro t ht
  refine ⟨((hΦ _ hp).2 t ht).1, ?_⟩
  have hd := ((hΦ _ hp).2 t ht).2
  have he : T (θ⁻¹ • a, Φ ((θ⁻¹ • a, x), t)) =
      ∑ j, a j • Z j (Φ ((θ⁻¹ • a, x), t)) := by
    dsimp [T, constantCombination]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul, ← mul_assoc,
      mul_inv_cancel₀ hθ.ne', one_mul]
  rw [he] at hd
  exact hd

end RothschildStein.G4
