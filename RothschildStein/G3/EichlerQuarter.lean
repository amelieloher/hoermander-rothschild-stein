-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EichlerIdentities
@[expose] public section
namespace RothschildStein.G3

/-- Eichler's quarter-scale identity for homogeneous cocycles modulo Lie
polynomials (BB (9.86), pp. 473–474). -/
theorem eichler_quarter {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup Q] [Module 𝕜 Q]
    (n : ℕ) (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0)
    (hh : ∀ (r : 𝕜) a b, P (r • a) (r • b) = r ^ n • P a b) (a b : V) :
    (1 - 2 * (1 / 2 : 𝕜) ^ n) • P a b =
      ((1 / 2 : 𝕜) ^ n * (1 + (-1 : 𝕜) ^ n)) • P (a + b) b := by
  have h := eichler_half_left P hc hcol a b
  rw [eichler_half_right P hc hcol ((1 / 2 : 𝕜) • a) b,
    eichler_half_right P hc hcol (-(1 / 2 : 𝕜) • a) (a + b)] at h
  have h2 : P ((1 / 2 : 𝕜) • a + b) (-(1 / 2 : 𝕜) • b) =
      -P ((1 / 2 : 𝕜) • (a + b)) ((1 / 2 : 𝕜) • b) := by
    have h := eichler_reflect_right P hc hcol
      ((1 / 2 : 𝕜) • a + b) (-(1 / 2 : 𝕜) • b)
    have he : ((1 / 2 : 𝕜) • a + b) + (-(1 / 2 : 𝕜) • b) =
        (1 / 2 : 𝕜) • (a + b) := by module
    have hn : -(-(1 / 2 : 𝕜) • b) = (1 / 2 : 𝕜) • b := by module
    rw [he, hn] at h
    exact h
  have h3 : P (-(1 / 2 : 𝕜) • a) ((1 / 2 : 𝕜) • (a + b)) =
      -P ((1 / 2 : 𝕜) • a) ((1 / 2 : 𝕜) • b) := by
    have h := eichler_reflect_left P hc hcol
      (-(1 / 2 : 𝕜) • a) ((1 / 2 : 𝕜) • (a + b))
    have he : (-(1 / 2 : 𝕜) • a) + (1 / 2 : 𝕜) • (a + b) =
        (1 / 2 : 𝕜) • b := by module
    have hn : -(-(1 / 2 : 𝕜) • a) = (1 / 2 : 𝕜) • a := by module
    rw [he, hn] at h
    exact h
  have h4 : P ((-(1 / 2 : 𝕜) • a) + (a + b)) (-(1 / 2 : 𝕜) • (a + b)) =
      -P ((1 / 2 : 𝕜) • b) ((1 / 2 : 𝕜) • (a + b)) := by
    have h := eichler_reflect_right P hc hcol
      ((-(1 / 2 : 𝕜) • a) + (a + b)) (-(1 / 2 : 𝕜) • (a + b))
    have he : ((-(1 / 2 : 𝕜) • a) + (a + b)) + (-(1 / 2 : 𝕜) • (a + b)) =
        (1 / 2 : 𝕜) • b := by module
    have hn : -(-(1 / 2 : 𝕜) • (a + b)) = (1 / 2 : 𝕜) • (a + b) := by module
    rw [he, hn] at h
    exact h
  rw [h2, h3, h4, hh, hh, hh, eichler_exchange n P hc hcol hh (a + b) b] at h
  have he : P a b = (2 * (1 / 2 : 𝕜) ^ n) • P a b +
      ((1 / 2 : 𝕜) ^ n * (1 + (-1 : 𝕜) ^ n)) • P (a + b) b := by
    calc
      P a b = _ := h
      _ = _ := by module
  rw [sub_smul, one_smul]
  apply sub_eq_iff_eq_add.mpr
  exact he.trans (add_comm _ _)
end RothschildStein.G3
