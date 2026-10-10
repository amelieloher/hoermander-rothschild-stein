-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.HomogeneousBounds
public import HeatKernel.Gaussian.RestrictedChain
import Mathlib.Tactic

/-! # Gaussian lower bounds on homogeneous groups

The horizontal short-chain construction and exact ball volumes turn a uniform
near-diagonal estimate into a global Gaussian lower bound. The kernel inputs are
the positive-time pointwise convolution law and the near-diagonal estimate.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein
open scoped ENNReal
namespace HeatKernel.Gaussian

/-- A positive near-diagonal bound and the pointwise semigroup law imply the
Gaussian lower estimate on a Carnot group, with explicit chain constants
for any positive spatial scale at most one. -/
theorem carnot_gaussian_lower_bound_of_near_diagonal {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → CarnotPoint G hq hqpos hspan → CarnotPoint G hq hqpos hspan → ℝ≥0∞)
    {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc : 0 < c)
    (hnear : ∀ s, 0 < s → ∀ z w, dist z w ≤ a * Real.sqrt s / 4 →
      ENNReal.ofReal (c / (CarnotPoint.volume G hq hqpos hspan).real
        (ball z (Real.sqrt s))) ≤ p s z w)
    (hconv : ∀ s u, 0 < s → 0 < u → ∀ z w,
      p (s + u) z w = ∫⁻ a, p s z a * p u a w ∂(CarnotPoint.volume G hq hqpos hspan))
    {t : ℝ} (ht : 0 < t) (x y : CarnotPoint G hq hqpos hspan) :
    let b := min (c * (a / 32) ^ G.homogeneousDimension) (1 / 2)
    ENNReal.ofReal (b * Real.exp (-((64 / a ^ 2) * Real.log (1 / b)) * (dist x y ^ 2 / t)) /
      (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t))) ≤ p t x y := by
  dsimp only
  let v := volume.real (horizontalBall (G.horizontalFields hq) 0 1)
  let e : ℝ := (a / 32) ^ G.homogeneousDimension
  let b : ℝ := min (c * e) (1 / 2)
  have hv : 0 < v := horizontal_unit_ball_volume_real_pos G hq hqpos hspan hw
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := pow_le_one₀ (by positivity)
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr (by linarith))
  have hb : 0 < b := lt_min (mul_pos hc he) (by norm_num)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hbase : b ≤ c * e := min_le_left _ _
  obtain ⟨n, centers, _, hn, hx, hy, hcount, hlinks⟩ :=
    exists_carnot_short_chain G hq hqpos hspan x y ht ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let τ : ℝ := t / (k + 1 : ℕ)
  let V : ℝ := v * (Real.sqrt τ) ^ G.homogeneousDimension
  let W : ℝ := v * (Real.sqrt t) ^ G.homogeneousDimension
  have hnR : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hτ : 0 < τ := div_pos ht hnR
  have hV : 0 < V := mul_pos hv (pow_pos (Real.sqrt_pos.mpr hτ) _)
  have hW : 0 < W := mul_pos hv (pow_pos (Real.sqrt_pos.mpr ht) _)
  have hτt : τ ≤ t := div_le_self ht.le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hVW : e * V ≤ W := by
    calc
      e * V ≤ V := mul_le_of_le_one_left hV.le he1
      _ ≤ W := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.sqrt_nonneg τ) (Real.sqrt_le_sqrt hτt) _) hv.le
  have hvol : ∀ j, j ≤ k → CarnotPoint.volume G hq hqpos hspan
      (ball (centers j) (a * Real.sqrt τ / 32)) = ENNReal.ofReal (e * V) := by
    intro j _
    rw [carnot_volume_ball_eq G hq hqpos hspan hw _ (by positivity), Real.rpow_natCast]
    congr 1
    dsimp [e, V, v]
    simp only [div_pow, mul_pow]
    ring
  have hnear' : ∀ z w, dist z w ≤ a * Real.sqrt τ / 4 → ENNReal.ofReal (c / V) ≤ p τ z w := by
    intro z w hzw
    simpa only [CarnotPoint.volumeReal_ball G hq hqpos hspan hw z (Real.sqrt_pos.mpr hτ)] using
      hnear τ hτ z w hzw
  have H := gaussian_lower_bound_of_restricted_chain (CarnotPoint.volume G hq hqpos hspan)
    p k centers (A := 64 / a ^ 2) (s := dist x y ^ 2 / t) hx hy hτ
    (mul_pos ha (Real.sqrt_pos.mpr hτ)) hc.le he hV hW hb hb1 hbase hVW
    (by convert hcount using 1; field_simp)
    (fun j hj => hlinks j (by omega)) hvol hnear' hconv
  have htime : ((k + 1 : ℕ) : ℝ) * τ = t := mul_div_cancel₀ _ hnR.ne'
  rw [htime] at H
  simpa only [CarnotPoint.volumeReal_ball G hq hqpos hspan hw x (Real.sqrt_pos.mpr ht)] using H

end HeatKernel.Gaussian
