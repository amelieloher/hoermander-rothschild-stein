-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondPhiFromGlobalWords
public import RothschildStein.H3.ZeroPhiFromGlobalLp
public import RothschildStein.H3.HorizontalPhiHalfRadius
public import RothschildStein.H3.FirstWordExtendedPhiInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n q : ℕ}

/-- Step 2: the actual Phi interpolation controls the half-radius
horizontal weak norm using only global input and second-word representatives. -/
theorem horizontalWeakENorm_halfRadius_bound_of_global_second_words
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (B : ℝ) (hB : 0 ≤ B)
    (hwords : ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
      ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I u d ∧
        MemLp d p volume ∧ eLpNorm d p volume ≤ ENNReal.ofReal B)
    {R : ℝ} (hR : 0 < R)
    (hlocal : memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u)
    (cE : ℝ) (hcE : 0 ≤ cE) :
    let N₀ := fun σ => (eLpNorm u p (volume.restrict (G2.gaugeBall G ν 0 (σ * R)))).toReal
    let N₁ := fun σ => (horizontalWeakENorm X (quasiballDomain G ν 0 (σ * R)) p u).toReal
    let N₂ := fun σ => (driftSecondWeakENorm X (quasiballDomain G ν 0 (σ * R)) p u).toReal
    phi (Ioo (1 / 2 : ℝ) 1) R 1 N₁ ≤
      ENNReal.ofReal R⁻¹ * phi (Ioo (1 / 2 : ℝ) 1) R 2 N₂ +
      ENNReal.ofReal (cE / R⁻¹) * phi (Ioo (1 / 2 : ℝ) 1) R 0 N₀ →
    horizontalWeakENorm X (quasiballDomain G ν 0 (R / 2)) p u ≤
      ENNReal.ofReal ((driftSecondWordFamily q).card * B / 2 +
        2 * cE * (eLpNorm u p volume).toReal) := by
  dsimp only
  intro hinterp
  have hC : 0 ≤ (driftSecondWordFamily q).card * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hhalf := phi_horizontalWeak_half_radius_le G ν X 0 hR p u hlocal
  have hsecond := phi_driftSecond_bound_of_global_words G ν X p u B hB hwords 0 hR
  have hzero := phi_zero_bound_of_global_memLp G ν hu 0 hR
  have hb := firstWord_bound_of_extendedPhi_interpolation hR ENNReal.toReal_nonneg hC hcE
    ENNReal.toReal_nonneg hhalf hinterp hsecond hzero
  have hsmall := memSobolevX_quasiball_restrict G ν 0 (by linarith : R / 2 ≤ R)
    driftWeight X 2 p u hlocal
  have hfin := horizontalWeakENorm_lt_top X _ p u hsmall
  calc
    _ = ENNReal.ofReal (horizontalWeakENorm X (quasiballDomain G ν 0 (R / 2)) p u).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hb

end RothschildStein.H3
