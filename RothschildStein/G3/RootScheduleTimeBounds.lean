-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RootTimedPrimitiveSchedules
public import RothschildStein.G3.QuasiCorrectionNormBounds
@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem rootTimedPrimitiveSchedule_time_bound {a : ℕ} (p : Fin a → ℕ+)
    (A : ℝ × List (Fin a)) (hne : A.2 ≠ []) {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hb : |A.1| ≤ B*δ^wordWeight p A.2)
    (Z : Fin a × ℝ) (hZ : Z ∈ rootTimedPrimitiveSchedule p A) :
    |Z.2| ≤ (max 1 B)^(p Z.1 : ℕ)*δ^(p Z.1 : ℕ) := by
  obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp hZ
  have hroot := quasiCorrection_root_le p A.2 hne hB hδ hb
  have hBroot : B^((wordWeight p A.2 : ℝ)⁻¹) ≤ max 1 B :=
    by
      simpa only [abs_of_nonneg hB] using
        (quasiCorrection_root_le_max p A.2 hne (b := B) (B := B)
          (by rw [abs_of_nonneg hB]))
  have ht : (|A.1|^((wordWeight p A.2 : ℝ)⁻¹))^(p b.1 : ℕ) ≤
      (max 1 B)^(p b.1 : ℕ)*δ^(p b.1 : ℕ) := by
    have hr := hroot.trans (mul_le_mul_of_nonneg_right hBroot hδ)
    have hp := pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg A.1) _) hr (p b.1 : ℕ)
    simpa only [mul_pow] using hp
  cases hbbool : b.2 <;>
    simpa only [hbbool,Bool.false_eq_true,ite_false,ite_true,abs_neg,
      abs_of_nonneg (pow_nonneg (Real.rpow_nonneg (abs_nonneg A.1) _) _)] using ht

theorem rootTimedFactorSchedule_time_bound {a : ℕ} (p : Fin a → ℕ+)
    (AS : List (ℝ × List (Fin a))) {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hAS : ∀ A ∈ AS, A.2 ≠ [] ∧ |A.1| ≤ B*δ^wordWeight p A.2)
    (Z : Fin a × ℝ) (hZ : Z ∈ rootTimedFactorSchedule p AS) :
    |Z.2| ≤ (max 1 B)^(p Z.1 : ℕ)*δ^(p Z.1 : ℕ) := by
  obtain ⟨A,hA,hZ⟩ := List.mem_flatMap.mp hZ
  exact rootTimedPrimitiveSchedule_time_bound p A (hAS A hA).1 hB hδ (hAS A hA).2 Z hZ
end RothschildStein.G3
