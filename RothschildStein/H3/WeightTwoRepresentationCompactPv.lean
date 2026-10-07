-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoHorizontal
public import RothschildStein.H3.CompactOperatorRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal

/-- the exact second-word representation and singular integral
Lp bounds give the compact estimate for all weight-two words. Drift is
derived from the operator identity; its estimate is not an input. -/
theorem compact_weight_two_estimate_of_representation_and_compact_lp_bounds {n q : ℕ}
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (p : ℝ≥0∞) (hp : 1 ≤ p) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (T : Fin q → Fin q → ((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ)
    (c : Fin q → Fin q → ℝ) (hc : ∀ i j, |c i j| ≤ B)
    (hT : ∀ i j f, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (T i j f) p volume ≤ ENNReal.ofReal M*eLpNorm f p volume)
    (hrep : ∀ u : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → ∀ i j : Fin q,
      wordDerivative X [i.succ,j.succ] u =ᵐ[volume]
        fun x => T i j (sumSquaresWithDrift X u) x + c i j*sumSquaresWithDrift X u x) :
    0 < (q+1 : ℝ)*(M+B+1) ∧
      ∀ u : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
        ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
          eLpNorm (wordDerivative X I u) p volume ≤
            ENNReal.ofReal ((q+1 : ℝ)*(M+B+1))*eLpNorm (sumSquaresWithDrift X u) p volume := by
  apply compact_weight_two_estimate_of_horizontal_bounds X p hp (add_nonneg hM hB)
  intro u hu huc i j
  rw [eLpNorm_congr_ae (hrep u hu huc i j)]
  have ht := hT i j (sumSquaresWithDrift X u)
    ((contDiff_sumSquaresWithDrift_compact X hX hu).of_le (by simp))
    (hasCompactSupport_sumSquaresWithDrift X huc)
  have hs : eLpNorm (fun x => c i j*sumSquaresWithDrift X u x) p volume ≤
      ENNReal.ofReal B*eLpNorm (sumSquaresWithDrift X u) p volume := by
    have he : (fun x => c i j*sumSquaresWithDrift X u x) =
        c i j • sumSquaresWithDrift X u := rfl
    rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hc i j)) le_rfl
  calc
    eLpNorm (fun x => T i j (sumSquaresWithDrift X u) x + c i j*sumSquaresWithDrift X u x) p volume
      ≤ eLpNorm (T i j (sumSquaresWithDrift X u)) p volume +
        eLpNorm (fun x => c i j*sumSquaresWithDrift X u x) p volume := eLpNorm_add_le hp
    _ ≤ ENNReal.ofReal M*eLpNorm (sumSquaresWithDrift X u) p volume +
        ENNReal.ofReal B*eLpNorm (sumSquaresWithDrift X u) p volume := add_le_add ht hs
    _ = ENNReal.ofReal (M+B)*eLpNorm (sumSquaresWithDrift X u) p volume := by
      rw [ENNReal.ofReal_add hM hB, add_mul]

end RothschildStein.H3
