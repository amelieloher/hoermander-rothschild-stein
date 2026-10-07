-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.JointSpatialBrackets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Iterating the joint spatial-bracket family agrees with the
actual adjoint iteration on every fixed parameter slice (BB pp. 441–443). -/
theorem spatialBracketFamily_iterate_slice {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z Y : P × E → E) (p : P) (k : ℕ) :
    (fun x => ((spatialBracketFamily Z)^[k] Y) (p, x)) =
      ((VectorField.lieBracket ℝ (fun x => Z (p, x)))^[k] (fun x => Y (p, x))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fun x => VectorField.lieBracket ℝ (fun y => Z (p, y))
      (fun y => ((spatialBracketFamily Z)^[k] Y) (p, y)) x) = _
    rw [ih]

/-- All actual adjoint families are jointly smooth on their
original parameter/spatial domain (BB Lemma 9.48, pp. 441–443). -/
theorem spatialBracketFamily_iterate_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {Z Y : P × E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((spatialBracketFamily Z)^[k] Y) S := by
  induction k with
  | zero => exact hY
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact spatialBracketFamily_contDiffOn hS hZ ih

/-- Joint parameter/spatial jets of an actual length-k adjoint
family retain the kth power of the small field's full jet bound, and lose
exactly k primitive jets (BB Lemma 9.48, pp. 441–443). -/
theorem norm_spatialBracketFamily_iterate_jet_le {P E : Type*} {R : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set (P × E)} (hS : IsOpen S) {Z Y : P × E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z S) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y S)
    {p : P × E} (hp : p ∈ S) {B F : ℝ}
    (hZjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Z p‖ ≤ B)
    (hYjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Y p‖ ≤ F)
    (k n : ℕ) (hnk : n + k ≤ R) :
    ‖iteratedFDeriv ℝ n ((spatialBracketFamily Z)^[k] Y) p‖ ≤
      (2 ^ (R + 1) * B) ^ k * F := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hZjet 0 (Nat.zero_le R))
  have hF : 0 ≤ F := (norm_nonneg _).trans (hYjet 0 (Nat.zero_le R))
  induction k generalizing n with
  | zero => simpa only [Function.iterate_zero, id_eq, pow_zero, one_mul] using hYjet n (by omega)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have htail : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j ((spatialBracketFamily Z)^[k] Y) p‖ ≤
        (2 ^ (R + 1) * B) ^ k * F := fun j hj => ih j (by omega)
    have hh := norm_spatialBracketFamily_jet_le (R := n + 1) hS hZ
      (spatialBracketFamily_iterate_contDiffOn hS hZ hY k) hp le_rfl
      (fun j hj => hZjet j (by omega)) htail
    apply hh.trans
    calc
      _ ≤ 2 ^ (R + 1) * B * ((2 ^ (R + 1) * B) ^ k * F) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by omega : n + 1 ≤ R + 1)) hB)
          (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) k) hF)
      _ = (2 ^ (R + 1) * B) ^ (k + 1) * F := by rw [pow_succ]; ring

end RothschildStein.G4
