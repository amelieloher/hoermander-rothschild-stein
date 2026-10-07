-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.WordInduction

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate ComplexInnerProductSpace
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

theorem sobolevNorm_lambda_zero (s : ℝ) (φ : TestFunction N) :
    sobolevNorm 0 (lambdaOperator s φ) = sobolevNorm s φ := by
  rw [sobolevNorm_eq_schwartzSobolevNorm, sobolevNorm_eq_schwartzSobolevNorm]
  have h := Hormander.A.Lambda_sobolevNorm s 0 φ
  rw [add_zero] at h
  exact h

/-- Sobolev duality for the Hermitian pairing on Schwartz functions. -/
theorem H_duality (a b : TestFunction N) (r : ℝ) :
    ‖hermitianPairing a b‖ ≤ sobolevNorm r a * sobolevNorm (-r) b := by
  have hp := Hormander.A.Lambda_pairing (N := N) r a b
  have e2 : ∀ (f g : Carrier N → ℂ), ∫ x, ⟪f x, g x⟫ = ∫ x, g x * conj (f x) := fun f g => by
    congr 1
  have h1 : hermitianPairing (lambdaOperator (-r) b) (lambdaOperator r a) = hermitianPairing b a := by
    unfold hermitianPairing
    have := hp
    rw [e2 _ _, e2 _ _] at this
    exact this
  have h2 : ‖hermitianPairing b a‖ ≤ sobolevNorm r a * sobolevNorm (-r) b := by
    rw [← h1]
    refine (norm_H_le _ _).trans ?_
    rw [sobolevNorm_lambda_zero, sobolevNorm_lambda_zero, mul_comm]
  rw [H_conj_symm a b, Complex.norm_conj]
  exact h2

/-- The Hermitian adjoint of a class operator exists and lies in the same class,
(iv)). -/
theorem B10Facts.class_adjoint (F : B10Facts N) {m : ℝ} {S : Operator N} (hS : OperatorClass m S) :
    ∃ Ss : Operator N, HasHermitianAdjoint S Ss ∧ OperatorClass m Ss := by
  obtain ⟨St, hSt, _⟩ := id hS
  exact ⟨conjOperator St, hSt.hasHermitianAdjoint, (F.transpose_mem m S St hS hSt).conj⟩

/-- Pairing bound with a class operator in the left slot. -/
theorem B10Facts.pairing_left (F : B10Facts N) {m : ℝ} {S : Operator N} (hS : OperatorClass m S)
    (s : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : TestFunction N,
      ‖hermitianPairing (S a) b‖ ≤ C * (sobolevNorm (s + m) a * sobolevNorm (-s) b) := by
  obtain ⟨Ss, hadj, hSs⟩ := F.class_adjoint hS
  obtain ⟨C, hC⟩ := hSs.hasOrder' (-(s + m))
  refine ⟨C, C.2, fun a b => ?_⟩
  rw [hadj]
  refine (H_duality a (Ss b) (s + m)).trans ?_
  have h := hC b
  have e : -(s + m) + m = -s := by ring
  rw [e] at h
  calc sobolevNorm (s + m) a * sobolevNorm (-(s + m)) (Ss b)
      ≤ sobolevNorm (s + m) a * (C * sobolevNorm (-s) b) :=
        mul_le_mul_of_nonneg_left h (sobolevNorm_nonneg _ _)
    _ = _ := by ring

/-- Pairing bound with a class operator in the right slot. -/
theorem B10Facts.pairing_right (F : B10Facts N) {m : ℝ} {S : Operator N} (hS : OperatorClass m S)
    (s : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : TestFunction N,
      ‖hermitianPairing a (S b)‖ ≤ C * (sobolevNorm (s + m) b * sobolevNorm (-s) a) := by
  obtain ⟨C, hC0, hC⟩ := F.pairing_left hS s
  refine ⟨C, hC0, fun a b => ?_⟩
  rw [H_conj_symm, Complex.norm_conj]
  exact hC b a

theorem lambdaOperator_comp_apply' (s t : ℝ) (u : TestFunction N) :
    lambdaOperator s (lambdaOperator t u) = lambdaOperator (s + t) u :=
  LinearMap.congr_fun (lambdaOperator_comp (N := N) s t) u

/-- The Sobolev norm squared as a pairing: `‖w‖²_{H^r} = Re (Λ^{2r} w, w)`. -/
theorem sobolevNorm_sq_eq_re_pairing (r : ℝ) (w : TestFunction N) :
    sobolevNorm r w ^ 2 = (hermitianPairing (lambdaOperator (2 * r) w) w).re := by
  have h1 : sobolevNorm r w = sobolevNorm 0 (lambdaOperator r w) := (sobolevNorm_lambda_zero r w).symm
  rw [h1, sobolevNorm_zero_sq]
  have hp := Hormander.A.Lambda_pairing (N := N) r w (lambdaOperator (2 * r) w)
  have e1 : (Hormander.A.Lambda (-r) (lambdaOperator (2 * r) w) : TestFunction N) =
      lambdaOperator r w := by
    change lambdaOperator (-r) (lambdaOperator (2 * r) w) = _
    rw [lambdaOperator_comp_apply']; ring_nf
  rw [e1] at hp
  have hp' : hermitianPairing (lambdaOperator r w) (lambdaOperator r w) =
      hermitianPairing (lambdaOperator (2 * r) w) w := by
    unfold hermitianPairing
    have e2 : ∀ (a b : Carrier N → ℂ), ∫ x, ⟪a x, b x⟫ = ∫ x, b x * conj (a x) := fun a b => by
      congr 1
    have hp2 := hp
    rw [e2 _ _, e2 _ _] at hp2
    exact hp2
  have := congrArg Complex.re hp'
  rw [H_self] at this
  simpa using this

theorem H_realMultiplier_left (g : SchwartzMap (Carrier N) ℝ) (a b : TestFunction N) :
    hermitianPairing (realMultiplierOperator g a) b = hermitianPairing a (realMultiplierOperator g b) := by
  unfold hermitianPairing
  congr 1; funext x
  have e : ∀ f : TestFunction N, realMultiplierOperator g f x = (g x : ℂ) * f x := fun f => by
    unfold realMultiplierOperator
    rw [multiplierOperator_apply, complexifyRealSchwartz_apply]
  rw [e, e]
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem H_vectorField_right (Y : RealSchwartzVectorField N) (a b : TestFunction N) :
    hermitianPairing a (vectorFieldOperator Y b) =
      -hermitianPairing (vectorFieldOperator Y a) b + hermitianPairing (realMultiplierOperator (negDiv Y) a) b := by
  have h := H_vectorField_left Y b a
  have h2 := congrArg (fun z => conj z) h
  simp only [map_add, map_neg] at h2
  rw [← H_conj_symm, ← H_conj_symm] at h2
  rw [h2, H_conj_symm (realMultiplierOperator (negDiv Y) a) b]

end Hormander.C
