-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FieldPowerBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Mixed powers in the two-flow Taylor polynomial consume the
sum of ordinary operator orders, with one common finite jet budget
(BB Lemma 9.22, pp. 413–414). -/
theorem norm_mixed_fieldPower_jet_le {N R : ℕ}
    (Ω : Opens (Fin N → ℝ)) (X Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j X x‖ ≤ B)
    (hYjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j Y x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (m n r : ℕ) (hmnr : r + m + n ≤ R) :
    ‖iteratedFDeriv ℝ r (fieldPower X m (fieldPower Y n f)) x‖ ≤
      (2 ^ R * B) ^ (m + n) * F := by
  have hF : 0 ≤ F := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le R))
  have hinner : ∀ j ≤ R - n,
      ‖iteratedFDeriv ℝ j (fieldPower Y n f) x‖ ≤ (2 ^ R * B) ^ n * F := by
    intro j hj
    exact norm_fieldPower_jet_le Ω Y hY f hf hx hYjet hfjet n j (by omega)
  have ho := norm_fieldPower_jet_le (R := R - n) Ω X hX (fieldPower Y n f)
    (contDiffOn_fieldPower Ω Y hY n f hf) hx
    (fun j hj => hXjet j (by omega)) hinner m r (by omega)
  apply ho.trans
  have hpow : (2 ^ (R - n) * B : ℝ) ^ m ≤ (2 ^ R * B) ^ m := by
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) hB)
    apply mul_le_mul_of_nonneg_right _ hB
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le R n)
  calc
    _ ≤ (2 ^ R * B) ^ m * ((2 ^ R * B) ^ n * F) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) _) hF)
    _ = _ := by rw [pow_add]; ring
end RothschildStein.G3
