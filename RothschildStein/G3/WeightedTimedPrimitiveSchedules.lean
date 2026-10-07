-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TimedPrimitiveLieInputs
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Polynomial dilation of fixed normalized primitive times. -/
def scaleTimedPrimitiveSchedule {a : ℕ} (p : Fin a → ℕ+) (t : ℝ)
    (S : List (Fin a × ℝ)) : List (Fin a × ℝ) :=
  S.map (fun b => (b.1,t^(p b.1 : ℕ)*b.2))

@[simp] theorem scaleTimedPrimitiveSchedule_length {a : ℕ} (p : Fin a → ℕ+)
    (t : ℝ) (S : List (Fin a × ℝ)) : (scaleTimedPrimitiveSchedule p t S).length = S.length :=
  List.length_map _

theorem scaleTimedPrimitiveSchedule_time_bound {a : ℕ} (p : Fin a → ℕ+)
    (t : ℝ) (S : List (Fin a × ℝ)) {A : ℝ}
    (hS : ∀ b ∈ S, |b.2| ≤ A) :
    ∀ b ∈ scaleTimedPrimitiveSchedule p t S, |b.2| ≤ A*|t| ^(p b.1 : ℕ) := by
  intro b hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  rw [abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_left (hS c hc) (pow_nonneg (abs_nonneg t) _)).trans_eq (mul_comm _ _)

theorem scaleTimedPrimitiveSchedule_coarse_time_bound {a : ℕ} (p : Fin a → ℕ+)
    (t : ℝ) (S : List (Fin a × ℝ)) {A : ℝ} (hA : 0 ≤ A) (ht : |t| ≤ 1)
    (hS : ∀ b ∈ S, |b.2| ≤ A) :
    ∀ b ∈ scaleTimedPrimitiveSchedule p t S, |b.2| ≤ A*|t| := by
  intro b hb
  apply (scaleTimedPrimitiveSchedule_time_bound p t S hS b hb).trans
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_of_le_one (abs_nonneg t) ht (p b.1).pos).trans_eq (pow_one _)) hA
end RothschildStein.G3
