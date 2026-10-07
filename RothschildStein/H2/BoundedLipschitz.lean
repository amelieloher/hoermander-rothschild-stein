-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal Topology ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- A globally bounded Lipschitz real function, with explicit finite constants.
BB Remark 7.8, p. 298; the abstract density proof uses this class. -/
def BoundedLipschitz (f : X → ℝ) : Prop :=
  ∃ L M : ℝ≥0, LipschitzWith L f ∧ ∀ x, |f x| ≤ M

/-- Constants are bounded Lipschitz functions. -/
theorem boundedLipschitz_const (c : ℝ) : BoundedLipschitz (fun _ : X => c) := by
  refine ⟨0, Real.toNNReal |c|, LipschitzWith.const c, ?_⟩
  intro x
  simp

/-- Bounded Lipschitz functions are stable under addition. -/
theorem BoundedLipschitz.add {f g : X → ℝ} (hf : BoundedLipschitz f)
    (hg : BoundedLipschitz g) : BoundedLipschitz (fun x => f x + g x) := by
  obtain ⟨L, M, hl, hm⟩ := hf
  obtain ⟨L', M', hl', hm'⟩ := hg
  refine ⟨L + L', M + M', LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    have h₁ := hl.dist_le_mul x y
    have h₂ := hl'.dist_le_mul x y
    rw [Real.dist_eq] at h₁ h₂ ⊢
    have he : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by simp; ring))
  · intro x
    exact (abs_add_le _ _).trans (by simpa using add_le_add (hm x) (hm' x))

/-- Scalar multiplication preserves the approximation class. -/
theorem BoundedLipschitz.const_mul {f : X → ℝ} (hf : BoundedLipschitz f) (c : ℝ) :
    BoundedLipschitz (fun x => c * f x) := by
  obtain ⟨L, M, hl, hm⟩ := hf
  refine ⟨Real.toNNReal |c| * L, Real.toNNReal |c| * M,
    LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    have he : c * f x - c * f y = c * (f x - f y) := by ring
    rw [Real.dist_eq, he, abs_mul]
    have hb := mul_le_mul_of_nonneg_left (hl.dist_le_mul x y) (abs_nonneg c)
    simpa [Real.dist_eq, Real.coe_toNNReal', max_eq_left (abs_nonneg c), mul_assoc] using hb
  · intro x
    simpa [abs_mul, Real.coe_toNNReal', max_eq_left (abs_nonneg c)] using
      mul_le_mul_of_nonneg_left (hm x) (abs_nonneg c)

/-- Lipschitz approximation to a closed-set indicator. -/
def closedApprox (s : Set X) (n : ℕ) (x : X) : ℝ :=
  max 0 (1 - (n : ℝ) * infDist x s)

/-- The closed-set approximations lie in [0,1]. -/
theorem closedApprox_bounds (s : Set X) (n : ℕ) (x : X) :
    0 ≤ closedApprox s n x ∧ closedApprox s n x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have h : 0 ≤ (n : ℝ) * infDist x s := mul_nonneg (Nat.cast_nonneg _) infDist_nonneg
  linarith

/-- Each closed-set approximation is bounded and globally n-Lipschitz. -/
theorem boundedLipschitz_closedApprox (s : Set X) (n : ℕ) :
    BoundedLipschitz (closedApprox s n) := by
  have hl : LipschitzWith (n : ℝ≥0) (fun x : X => 1 - (n : ℝ) * infDist x s) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : (1 - (n : ℝ) * infDist x s) - (1 - (n : ℝ) * infDist y s) =
        -(n : ℝ) * (infDist x s - infDist y s) := by ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    simpa [Real.dist_eq] using mul_le_mul_of_nonneg_left
      ((lipschitz_infDist_pt s).dist_le_mul x y) (Nat.cast_nonneg n)
  refine ⟨n, 1, hl.const_max 0, ?_⟩
  intro x
  simpa [abs_of_nonneg (closedApprox_bounds s n x).1] using (closedApprox_bounds s n x).2

/-- These bounded Lipschitz functions converge to the closed-set indicator. -/
theorem tendsto_closedApprox {s : Set X} (hs : IsClosed s) (hne : s.Nonempty) (x : X) :
    Tendsto (fun n => closedApprox s n x) atTop (𝓝 (s.indicator (fun _ => (1 : ℝ)) x)) := by
  classical
  by_cases hx : x ∈ s
  · simp [closedApprox, infDist_zero_of_mem hx, hx]
  · have hd := (hs.notMem_iff_infDist_pos hne).mp hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist x s)
    have hNm : 1 < (N : ℝ) * infDist x s := (div_lt_iff₀ hd).mp hN
    have he : ∀ᶠ n : ℕ in atTop, closedApprox s n x = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      unfold closedApprox
      rw [max_eq_left]
      nlinarith
    simpa [hx] using (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm) :
      Tendsto (fun n => closedApprox s n x) atTop (𝓝 (0 : ℝ)))

end RothschildStein.H2
