-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeakComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ}

/-- A C2 subsolution tending to zero at coordinate infinity is
nonpositive, using the exact exponential barrier identity
(BB Cor 1.58, p. 38). -/
theorem nonpos_of_subsolution_decay_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) (γ : ℝ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hX : ∀ i : Fin q, Differentiable ℝ (X i.succ))
    (hP : ∀ z, 0 ≤ sumSquaresWithDrift X f z)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → ‖f z‖ ≤ ε)
    (x : Fin N → ℝ) : f x ≤ 0 := by
  have H (ε : ℝ) (hε : 0 < ε) : f x ≤ ε := by
    obtain ⟨R, hR⟩ := hdecay ε hε
    let r := max R ‖x‖ + 1
    have hx : x ∈ Metric.ball (0 : Fin N → ℝ) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (le_max_right _ _) (by dsimp [r]; linarith)
    apply weak_comparison_boundary_of_barrier j γ hbar Metric.isOpen_ball
      (Metric.isBounded_ball) hf.contDiffOn hf.continuous.continuousOn
      (fun i => (hX i).differentiableOn) (fun z _ => hP z) _ x (subset_closure hx)
    intro z hz
    have hout : z ∉ Metric.ball (0 : Fin N → ℝ) r := by
      have H : z ∈ closure (Metric.ball (0 : Fin N → ℝ) r) ∧
          z ∉ Metric.ball (0 : Fin N → ℝ) r := by
        simpa only [frontier, Metric.isOpen_ball.interior_eq, Set.mem_sdiff] using hz
      exact H.2
    have hzr : r ≤ ‖z‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hout
    have hRR : R ≤ r := (le_max_left _ _).trans (by dsimp [r]; linarith)
    exact (le_abs_self (f z)).trans (hR z (hRR.trans hzr))
  by_contra hn
  have hp : 0 < f x := lt_of_not_ge hn
  have h := H (f x / 2) (half_pos hp)
  linarith

/-- A null solution tending to zero at infinity vanishes
(BB Cor 1.58, p. 38). -/
theorem eq_zero_of_null_solution_decay_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) (γ : ℝ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (hX : ∀ i : Fin q, Differentiable ℝ (X i.succ))
    (hP : ∀ z, sumSquaresWithDrift X f z = 0)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → ‖f z‖ ≤ ε) : f = 0 := by
  have hpos : ∀ x, f x ≤ 0 := nonpos_of_subsolution_decay_of_barrier j γ hbar hf hX
    (fun z => (hP z).ge) hdecay
  have hneg : ∀ x, (-f) x ≤ 0 := nonpos_of_subsolution_decay_of_barrier j γ hbar hf.neg hX
    (fun z => by
      have H := congrFun (sumSquares_const_mul X (-1) f) z
      have he : (fun x => -1 * f x) = -f := by
        funext x
        simp only [neg_one_mul, Pi.neg_apply]
      rw [he, hP z, mul_zero] at H
      rw [H])
    (fun ε hε => by
      obtain ⟨R, hR⟩ := hdecay ε hε
      exact ⟨R, fun z hz => by simpa only [Pi.neg_apply, norm_neg] using hR z hz⟩)
  funext x
  change f x = 0
  have hn := hneg x
  change -f x ≤ 0 at hn
  exact le_antisymm (hpos x) (neg_nonpos.mp hn)

end RothschildStein.H1
