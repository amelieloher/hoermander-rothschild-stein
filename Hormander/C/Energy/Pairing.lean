-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Energy.Adjoint

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate

namespace Hormander.C

open Hormander.B

variable {N : ℕ}

/-- The squared `L²` norm of a Schwartz function. -/
def normSq (u : TestFunction N) : ℝ := ∫ x, ‖u x‖ ^ 2

theorem integrable_sqnorm (u : TestFunction N) : Integrable (fun x => ‖u x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm u.continuous.aestronglyMeasurable).mp (u.memLp 2 volume)

theorem normSq_nonneg (u : TestFunction N) : 0 ≤ normSq u :=
  integral_nonneg fun x => by positivity

theorem integrable_pair (u v : TestFunction N) :
    Integrable (fun x => u x * conj (v x)) volume := by
  have := integrable_mul_test u (conjTest v)
  simpa using this

theorem H_self (u : TestFunction N) : hermitianPairing u u = (normSq u : ℂ) := by
  unfold hermitianPairing normSq
  rw [← integral_complex_ofReal]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem H_conj_symm (u v : TestFunction N) :
    hermitianPairing u v = conj (hermitianPairing v u) := by
  unfold hermitianPairing
  rw [← integral_conj]
  congr 1; funext x
  simp [mul_comm]

theorem H_add_left (u v w : TestFunction N) :
    hermitianPairing (u + v) w = hermitianPairing u w + hermitianPairing v w := by
  unfold hermitianPairing
  rw [← integral_add (integrable_pair u w) (integrable_pair v w)]
  congr 1; funext x
  simp [add_mul]

theorem H_neg_right (u v : TestFunction N) :
    hermitianPairing u (-v) = -hermitianPairing u v := by
  unfold hermitianPairing
  rw [← integral_neg]
  congr 1; funext x
  simp

theorem H_add_right (u v w : TestFunction N) :
    hermitianPairing u (v + w) = hermitianPairing u v + hermitianPairing u w := by
  rw [H_conj_symm, H_add_left, map_add, ← H_conj_symm, ← H_conj_symm]

theorem H_zero_left (w : TestFunction N) : hermitianPairing 0 w = 0 := by
  unfold hermitianPairing; simp

theorem H_sum_left {ι : Type*} (I : Finset ι) (u : ι → TestFunction N) (w : TestFunction N) :
    hermitianPairing (∑ i ∈ I, u i) w = ∑ i ∈ I, hermitianPairing (u i) w := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [H_zero_left]
  | insert i I hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H_add_left, ih]

theorem H_re_symm (u v : TestFunction N) :
    (hermitianPairing u v).re = (hermitianPairing v u).re := by
  rw [H_conj_symm u v]; simp

/-- Pairing with a real multiplier against the function itself. -/
theorem H_realMultiplier (g : SchwartzMap (Carrier N) ℝ) (φ : TestFunction N) :
    (hermitianPairing (realMultiplierOperator g φ) φ).re = ∫ x, g x * ‖φ x‖ ^ 2 := by
  have h : hermitianPairing (realMultiplierOperator g φ) φ =
      ((∫ x, g x * ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    unfold hermitianPairing
    rw [← integral_complex_ofReal]
    congr 1; funext x
    have : realMultiplierOperator g φ x = (g x : ℂ) * φ x := by
      unfold realMultiplierOperator
      rw [multiplierOperator_apply, complexifyRealSchwartz_apply]
    rw [this]
    have h2 : φ x * conj (φ x) = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc (g x : ℂ) * φ x * conj (φ x) = (g x : ℂ) * (φ x * conj (φ x)) := by ring
      _ = _ := by rw [h2]; push_cast; ring
  rw [h]; simp

end Hormander.C
