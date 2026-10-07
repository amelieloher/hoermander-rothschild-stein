-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EichlerQuarter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Order.GroupWithZero.Basic
@[expose] public section
namespace RothschildStein.G3

/-- Eichler's homogeneous-cocycle criterion: in degree at least three,
collinear vanishing and the cocycle identity force the cocycle to vanish. This
works over the rationals as well as the reals, retaining rational Lie coefficients
(BB (9.80)–(9.86), pp. 472–474). -/
theorem eichler_cocycle_eq_zero {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup Q] [Module 𝕜 Q]
    (n : ℕ) (hn : 3 ≤ n) (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0)
    (hh : ∀ (r : 𝕜) a b, P (r • a) (r • b) = r ^ n • P a b) :
    ∀ a b, P a b = 0 := by
  let t : 𝕜 := (1 / 2) ^ n
  have htpos : 0 < t := pow_pos (by norm_num) n
  have htbound : t ≤ (1 / 8 : 𝕜) := by
    have h := pow_le_pow_of_le_one (show (0 : 𝕜) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : 𝕜) ≤ 1 by norm_num) hn
    norm_num at h
    exact h
  have hsign : -(1 : 𝕜) ≤ (-1 : 𝕜) ^ n ∧ (-1 : 𝕜) ^ n ≤ 1 := by
    apply abs_le.mp
    rw [abs_pow]
    norm_num
  let d : 𝕜 := 1 - 2 * t
  let z : 𝕜 := t * (1 + (-1 : 𝕜) ^ n)
  let r : 𝕜 := z / d
  have hd : 0 < d := by dsimp [d]; linarith
  have hz0 : 0 ≤ z := mul_nonneg (le_of_lt htpos) (by linarith [hsign.1])
  have hzbound : z ≤ 2 * t := by
    dsimp [z]
    have h := mul_le_mul_of_nonneg_left (show 1 + (-1 : 𝕜) ^ n ≤ 2 by linarith [hsign.2])
      (le_of_lt htpos)
    simpa only [mul_comm] using h
  have hr0 : 0 ≤ r := div_nonneg hz0 (le_of_lt hd)
  have hrbound : r ≤ (1 / 3 : 𝕜) := by
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    linarith
  have hscale : ∀ a b, P a b = r • P (a + b) b := by
    intro a b
    have h := eichler_quarter n P hc hcol hh a b
    change d • P a b = z • P (a + b) b at h
    have he := congrArg (fun q : Q => d⁻¹ • q) h
    rw [smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hd), one_smul] at he
    simpa only [r, div_eq_mul_inv, mul_comm] using he
  have hrec : ∀ a b, P a b = -(r • P a (-b)) := by
    intro a b
    have h := eichler_reflect_right P hc hcol a b
    rw [hscale (a + b) (-b)] at h
    have he : (a + b) + -b = a := by abel
    rw [he] at h
    exact h
  intro a b
  have he : P a b = r ^ 2 • P a b := by
    calc
      P a b = -(r • P a (-b)) := hrec a b
      _ = -(r • (-(r • P a (-(-b))))) := by rw [hrec a (-b)]
      _ = r ^ 2 • P a b := by rw [neg_neg]; module
  have hzero : (1 - r ^ 2) • P a b = 0 := by
    simpa only [sub_smul, one_smul] using sub_eq_zero.mpr he
  have hrs : r * r ≤ (1 / 3 : 𝕜) * (1 / 3 : 𝕜) := mul_self_le_mul_self hr0 hrbound
  have hne : (1 - r ^ 2 : 𝕜) ≠ 0 := by nlinarith
  have he0 := congrArg (fun q : Q => (1 - r ^ 2)⁻¹ • q) hzero
  simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using he0
end RothschildStein.G3
