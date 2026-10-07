-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalSecondNormFromGlobalWords
public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.H3.PhiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n q : ℕ}

/-- Step 2: the actual second Phi is bounded by R^2/4 times
the global second-word bound, with exact finite-family cardinality. -/
theorem phi_driftSecond_bound_of_global_words
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hwords : ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
      ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I u d ∧
        MemLp d p volume ∧ eLpNorm d p volume ≤ ENNReal.ofReal B)
    (x₀ : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    phi (Ioo (1 / 2 : ℝ) 1) R 2
      (fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ * R)) p u).toReal) ≤
      ENNReal.ofReal ((R ^ 2 / 4) * ((driftSecondWordFamily q).card * B)) := by
  have hC : 0 ≤ (driftSecondWordFamily q).card * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hb := phi_le_uniform_bound (B := (driftSecondWordFamily q).card * B)
    (N := fun σ => (driftSecondWeakENorm X (quasiballDomain G ν x₀ (σ * R)) p u).toReal)
    (Ioo (1 / 2 : ℝ) 1) 2 hR hC (fun _ h => ⟨h.1.le, h.2⟩)
    (fun σ _ => ⟨ENNReal.toReal_nonneg, by
      have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (driftSecondWeakENorm_local_bound_of_global_words X p u B hB hwords
          (quasiballDomain G ν x₀ (σ * R)))
      simpa only [ENNReal.toReal_ofReal hC] using hn⟩)
  convert hb using 1
  congr 1
  ring

end RothschildStein.H3
