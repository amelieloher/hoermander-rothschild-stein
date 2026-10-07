-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakJetNormFacts
public import RothschildStein.Definitions.sobolevXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- Restriction does not increase the Sobolev norm `sobolevXENorm` on actual weak jets. -/
theorem sobolevXENorm_mono_domain {n m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (V U : Opens (Fin n → ℝ)) (hUV : (U : Set (Fin n → ℝ)) ⊆ V)
    (k : ℕ) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X V k p f) :
    sobolevXENorm w X U k p f ≤ sobolevXENorm w X V k p f := by
  unfold sobolevXENorm
  apply Finset.sum_le_sum
  intro I hI
  obtain ⟨g, hg, _⟩ := hf.2 I hI
  exact weakWordENorm_mono_domain X V U hUV I p f g hg

end RothschildStein.H3
