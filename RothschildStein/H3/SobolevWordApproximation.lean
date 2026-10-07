-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.H3.CompactWordLp
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped Topology ENNReal

/-- Global order-two density in the weak Sobolev word representation.
Uniqueness makes convergence independent of the selected weak representative. -/
structure SobolevWordApproximation {n m : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (p : ℝ≥0∞)
    (u : (Fin n → ℝ) → ℝ) where
  functions : ℕ → (Fin n → ℝ) → ℝ
  smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (functions k)
  compact : ∀ k, HasCompactSupport (functions k)
  zero : Tendsto (fun k => eLpNorm (functions k-u) p volume) atTop (𝓝 0)
  word : ∀ I ∈ wordFamily w 2, ∀ g : (Fin n → ℝ) → ℝ,
    hasWeakWordDeriv X ⊤ I u g → MemLp g p volume →
    Tendsto (fun k => eLpNorm (wordDerivative X I (functions k)-g) p volume) atTop (𝓝 0)

end RothschildStein.H3
