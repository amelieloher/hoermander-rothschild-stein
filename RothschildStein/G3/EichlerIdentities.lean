-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Abel
@[expose] public section
namespace RothschildStein.G3

/-- Eichler's first reflection identity for a cocycle modulo Lie
polynomials (BB (9.81), p. 473). -/
theorem eichler_reflect_right {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Q] [Module 𝕜 Q] (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0) (a b : V) :
    P a b = -P (a + b) (-b) := by
  have h := hc a b (-b)
  have h0 : P a 0 = 0 := by simpa using hcol a 1 0
  have hneg : P b (-b) = 0 := by simpa using hcol b 1 (-1)
  rw [add_neg_cancel, h0, hneg, add_zero] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h

/-- Eichler's second reflection identity (BB (9.82), p. 473). -/
theorem eichler_reflect_left {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Q] [Module 𝕜 Q] (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0) (a b : V) :
    P a b = -P (-a) (a + b) := by
  have h := hc (-a) a b
  have h0 : P 0 b = 0 := by simpa using hcol b 0 1
  have hneg : P (-a) a = 0 := by simpa using hcol a (-1) 1
  rw [neg_add_cancel, h0, hneg, add_zero] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

/-- Eichler's exchange identity uses homogeneous degree n, with the
simultaneous sign reversal kept explicit (BB (9.83), p. 473). -/
theorem eichler_exchange {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Q] [Module 𝕜 Q] (n : ℕ) (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0)
    (hh : ∀ (r : 𝕜) a b, P (r • a) (r • b) = r ^ n • P a b) (a b : V) :
    P b a = -((-1 : 𝕜) ^ n • P a b) := by
  have hsum : -b + (b + a) = a := by abel
  have hsum' : a + (-(b + a)) = -b := by abel
  calc
    P b a = -P (-b) (b + a) := eichler_reflect_left P hc hcol b a
    _ = P a (-(b + a)) := by
      rw [eichler_reflect_right P hc hcol (-b) (b + a), hsum, neg_neg]
    _ = -P (-a) (-b) := by
      rw [eichler_reflect_left P hc hcol a (-(b + a)), hsum']
    _ = -((-1 : 𝕜) ^ n • P a b) := by
      rw [show P (-a) (-b) = (-1 : 𝕜) ^ n • P a b by simpa only [neg_one_smul] using hh (-1) a b]

/-- Halving the second argument in Eichler's cocycle (BB (9.84), p. 473). -/
theorem eichler_half_right {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Q] [Module 𝕜 Q] (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0) (a b : V) :
    P a b = P a ((1 / 2 : 𝕜) • b) - P (a + b) (-(1 / 2 : 𝕜) • b) := by
  have h := hc a b (-(1 / 2 : 𝕜) • b)
  have he : b + (-(1 / 2 : 𝕜) • b) = (1 / 2 : 𝕜) • b := by module
  have hz : P b (-(1 / 2 : 𝕜) • b) = 0 := by
    simpa only [one_smul] using hcol b 1 (-(1 / 2))
  rw [he, hz, add_zero] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h

/-- Halving the first argument in Eichler's cocycle (BB (9.85), p. 473). -/
theorem eichler_half_left {𝕜 V Q : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Q] [Module 𝕜 Q] (P : V → V → Q)
    (hc : ∀ a b c, P (a + b) c + P a b = P a (b + c) + P b c)
    (hcol : ∀ (v : V) (r t : 𝕜), P (r • v) (t • v) = 0) (a b : V) :
    P a b = P ((1 / 2 : 𝕜) • a) b - P (-(1 / 2 : 𝕜) • a) (a + b) := by
  have h := hc (-(1 / 2 : 𝕜) • a) a b
  have he : (-(1 / 2 : 𝕜) • a) + a = (1 / 2 : 𝕜) • a := by module
  have hz : P (-(1 / 2 : 𝕜) • a) a = 0 := by
    simpa only [one_smul] using hcol a (-(1 / 2)) 1
  rw [he, hz, add_zero] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using h.symm
end RothschildStein.G3
