-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.BallTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

private theorem contDiff_product :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  apply (AnalyticOnNhd.eval_mvPolynomial (G.productPolynomial j)).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl k => exact (contDiff_apply ℝ ℝ k).comp contDiff_fst
  | inr k => exact (contDiff_apply ℝ ℝ k).comp contDiff_snd

private theorem continuous_difference :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul (G.inv p.2) p.1) := by
  have hi : Continuous G.inv := continuous_pi fun j =>
    MvPolynomial.continuous_eval (p := G.inversePolynomial j)
  apply continuous_pi
  intro j
  change Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    MvPolynomial.eval (Sum.elim (G.inv p.2) p.1) (G.productPolynomial j))
  have harg : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => Sum.elim (G.inv p.2) p.1) := by
    apply continuous_pi
    intro i
    cases i with
    | inl k => exact (continuous_apply k).comp (hi.comp continuous_snd)
    | inr k => exact (continuous_apply k).comp continuous_fst
  exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp harg


/-- Polynomial multiplication has uniform Lipschitz bounds in either
argument on every bounded coordinate patch (BB Prop 3.17, pp. 103–104, strengthened). -/
theorem product_lipschitz_on_bounded (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Fin N → ℝ,
      ‖a‖ ≤ R → ‖b‖ ≤ R → ‖b'‖ ≤ R →
      ‖G.mul a b - G.mul a b'‖ ≤ C * ‖b - b'‖ ∧
      ‖G.mul b a - G.mul b' a‖ ≤ C * ‖b - b'‖ := by
  obtain ⟨K, hK⟩ := (contDiff_product G).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : (Fin N → ℝ) × (Fin N → ℝ)) R)
      (isCompact_closedBall _ _)
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro a b b' ha hb hb'
  have hab : (a, b) ∈ Metric.closedBall (0 : (Fin N → ℝ) × (Fin N → ℝ)) R := by
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro ha hb
  have hab' : (a, b') ∈ Metric.closedBall (0 : (Fin N → ℝ) × (Fin N → ℝ)) R := by
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro ha hb'
  have hba : (b, a) ∈ Metric.closedBall (0 : (Fin N → ℝ) × (Fin N → ℝ)) R := by
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro hb ha
  have hb'a : (b', a) ∈ Metric.closedBall (0 : (Fin N → ℝ) × (Fin N → ℝ)) R := by
    simpa [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff] using And.intro hb' ha
  constructor
  · have h := hK.dist_le_mul _ hab _ hab'
    have h' : ‖G.mul a b - G.mul a b'‖ ≤ (K : ℝ) * ‖b - b'‖ := by
      simpa [dist_eq_norm] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · have h := hK.dist_le_mul _ hba _ hb'a
    have h' : ‖G.mul b a - G.mul b' a‖ ≤ (K : ℝ) * ‖b - b'‖ := by
      simpa [dist_eq_norm] using h
    exact h'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Gauge and Euclidean distances are uniformly comparable on each bounded patch, with the stated upper exponent (BB Proposition 3.17, pp. 103–104). -/
theorem gaugeDistance_norm_comparison {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (R : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ x y : Fin N → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖x - y‖ ≤ C₁ * gaugeDistance G ν x y ∧
      gaugeDistance G ν x y ≤ C₂ * ‖x - y‖ ^ ((maxWeight G : ℝ)⁻¹) := by
  have hi : Continuous G.inv := continuous_pi fun j =>
    MvPolynomial.continuous_eval (p := G.inversePolynomial j)
  have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      ‖G.mul (G.inv p.2) p.1‖) := (continuous_difference G).norm
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : Fin N → ℝ) R).prod
    (isCompact_closedBall (0 : Fin N → ℝ) R)).bddAbove_image hc.continuousOn
  obtain ⟨I, hI⟩ := (isCompact_closedBall (0 : Fin N → ℝ) R).bddAbove_image
    (continuous_norm.comp hi).continuousOn
  obtain ⟨a, b, ha, hb, hνb⟩ := gauge_norm_comparison hν M
  obtain ⟨L, hL, hLb⟩ := product_lipschitz_on_bounded G (max 0 (max R M))
  obtain ⟨L', hL', hL'b⟩ := product_lipschitz_on_bounded G (max 0 (max R I))
  let d : ℝ := (maxWeight G : ℝ)⁻¹
  have hd : 0 ≤ d := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine ⟨L / a, b * L' ^ d, div_pos hL ha,
    mul_pos hb (Real.rpow_pos_of_pos hL' _), ?_⟩
  intro x y hx hy
  have hxB : x ∈ Metric.closedBall (0 : Fin N → ℝ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hyB : y ∈ Metric.closedBall (0 : Fin N → ℝ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  let z := G.mul (G.inv y) x
  have hz : ‖z‖ ≤ M := hM ⟨(x, y), ⟨hxB, hyB⟩, rfl⟩
  have hiy : ‖G.inv y‖ ≤ I := hI ⟨y, hyB, rfl⟩
  have hex : G.mul y z = x := (gaugeLeftTranslation G y).apply_symm_apply x
  have hey : G.mul y 0 = y := G.zero_right y
  have hizero : G.mul (G.inv y) y = 0 := G.inverse_left y
  have hzero : ‖(0 : Fin N → ℝ)‖ ≤ max 0 (max R M) := by simp
  have hdiff : ‖x - y‖ ≤ L * ‖z‖ := by
    have h := (hLb y z 0 (hy.trans ((le_max_left R M).trans (le_max_right 0 _)))
      (hz.trans ((le_max_right R M).trans (le_max_right 0 _))) hzero).1
    simpa only [hex, hey, sub_zero] using h
  have hz' : ‖z‖ ≤ L' * ‖x - y‖ := by
    have h := (hL'b (G.inv y) x y
      (hiy.trans ((le_max_right R I).trans (le_max_right 0 _)))
      (hx.trans ((le_max_left R I).trans (le_max_right 0 _)))
      (hy.trans ((le_max_left R I).trans (le_max_right 0 _)))).1
    simpa only [hizero, sub_zero] using h
  constructor
  · have hn : ‖z‖ ≤ ν z / a := (le_div_iff₀ ha).mpr
      (by simpa only [mul_comm] using (hνb z hz).1)
    calc
      ‖x - y‖ ≤ L * ‖z‖ := hdiff
      _ ≤ L * (ν z / a) := mul_le_mul_of_nonneg_left hn hL.le
      _ = L / a * gaugeDistance G ν x y := by unfold gaugeDistance; dsimp [z]; ring
  · change ν z ≤ _
    calc
      ν z ≤ b * ‖z‖ ^ d := (hνb z hz).2
      _ ≤ b * (L' * ‖x - y‖) ^ d := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hz' hd) hb.le
      _ = b * L' ^ d * ‖x - y‖ ^ d := by rw [Real.mul_rpow hL'.le (norm_nonneg _), mul_assoc]

end RothschildStein.G2
