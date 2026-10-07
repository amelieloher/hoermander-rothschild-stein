-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.HadamardFactor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- The next derivative of tH(t) at zero is exactly the
corresponding derivative of H multiplied by its order. This identifies
the smooth factors used by signed quasiexponentials (BB pp. 28–34). -/
theorem iteratedDeriv_mul_id_zero (H : ℝ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (j : ℕ) :
    iteratedDeriv (j + 1) (fun t => t * H t) 0 =
      (j + 1 : ℕ) * iteratedDeriv j H 0 := by
  rw [iteratedDeriv_fun_mul (f := fun t : ℝ => t) (g := H) (contDiffAt_id : ContDiffAt ℝ (j + 1) (fun t : ℝ => t) 0)
    ((hH.of_le (by simp)).contDiffAt)]
  simp only [iteratedDeriv_fun_id_zero]
  have hmem : (1 : ℕ) ∈ Finset.range (j + 2) := by
    simp only [Finset.mem_range]
    omega
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Nat.choose_one_right, hmem]

/-- A jointly smooth scalar map whose first k scalar-time jets
vanish has a jointly smooth exact t^k factor, also at t=0. This repeated
FTC factorization uses no division across the zero-time hyperplane
(BB Proposition 1.50, pp. 28–29; weighted quasiexponential step). -/
theorem exists_smooth_scalar_power_factor {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E]
    (k : ℕ) (G : E × ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hzero : ∀ x, ∀ j < k, iteratedDeriv j (fun t => G (x, t)) 0 = 0) :
    ∃ H : E × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) H ∧
      ∀ x t, G (x, t) = t ^ k * H (x, t) := by
  induction k generalizing G with
  | zero => exact ⟨G, hG, fun _ _ => by simp⟩
  | succ k ih =>
    have hz : ∀ x, G (x, 0) = 0 := fun x => by
      simpa only [iteratedDeriv_zero] using hzero x 0 (Nat.zero_lt_succ k)
    obtain ⟨H, hH, he⟩ := exists_smooth_hadamardFactor G hG hz
    have hflat : ∀ x, ∀ j < k, iteratedDeriv j (fun t => H (x, t)) 0 = 0 := by
      intro x j hj
      have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun t => H (x, t)) :=
        hH.comp (contDiff_const.prodMk contDiff_id)
      have hfun : (fun t => G (x, t)) = (fun t => t * H (x, t)) := by
        funext t
        simpa only [smul_eq_mul] using he x t
      have hh := hzero x (j + 1) (Nat.succ_lt_succ hj)
      rw [hfun, iteratedDeriv_mul_id_zero _ hslice j] at hh
      exact (mul_eq_zero.mp hh).resolve_left (by positivity)
    obtain ⟨K, hK, hfactor⟩ := ih H hH hflat
    refine ⟨K, hK, ?_⟩
    intro x t
    rw [he x t]
    simp only [smul_eq_mul, hfactor x t, pow_succ]
    ring

end RothschildStein.G1
