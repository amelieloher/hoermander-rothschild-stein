-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalSecondHolderLoss
public import Mathlib.Basic.ENNReal.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped ENNReal
namespace RothschildStein.H3

/-- The real loss calculation controls the extended full norms.
Finiteness of the output is derived from the actual estimate. -/
theorem local_second_holder_loss_ennreal {α γ R A B C D : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, ∀ F U ψ Ψ : ℝ≥0∞,
      0 < d → d ≤ R → F < ⊤ → U < ⊤ → ψ < ⊤ →
      ψ.toReal ≤ F.toReal / 2 + C * d ^ (-γ) * U.toReal →
      Ψ ≤ ENNReal.ofReal (A * d ^ (-α)) * F +
        ENNReal.ofReal (B * d ^ (-(2 + α))) * ψ + ENNReal.ofReal D * U →
      Ψ ≤ ENNReal.ofReal (K * d ^ (-(2 + α + γ))) * (F + U) := by
  obtain ⟨K, hK, hb⟩ := local_second_holder_loss_bound hα hγ hR hA hB hC hD
  refine ⟨K, hK, ?_⟩
  intro d F U ψ Ψ hd hdR hF hU hψ hi he
  have hright : ENNReal.ofReal (A * d ^ (-α)) * F +
      ENNReal.ofReal (B * d ^ (-(2 + α))) * ψ + ENNReal.ofReal D * U < ⊤ := by
    finiteness
  have hΨ : Ψ < ⊤ := he.trans_lt hright
  have heR := ENNReal.toReal_mono hright.ne he
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at heR
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hA (Real.rpow_nonneg hd.le _)),
    ENNReal.toReal_ofReal (mul_nonneg hB (Real.rpow_nonneg hd.le _)),
    ENNReal.toReal_ofReal hD] at heR
  have hfinal := hb d F.toReal U.toReal ψ.toReal Ψ.toReal hd hdR
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hi heR
  rw [← ENNReal.ofReal_toReal hΨ.ne]
  calc
    ENNReal.ofReal Ψ.toReal ≤ ENNReal.ofReal
      (K * d ^ (-(2 + α + γ)) * (F.toReal + U.toReal)) := ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal (K * d ^ (-(2 + α + γ))) * (F + U) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hd.le _)),
        ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hF.ne, ENNReal.ofReal_toReal hU.ne]

end RothschildStein.H3
