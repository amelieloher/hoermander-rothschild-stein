-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalWeakWordFromLocalScaleBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n m : ℕ}

/-- The first-word interpolation bound can be passed to the global
weak derivative with no pre-existing global derivative assumption. -/
theorem exists_global_weakWord_of_uniform_local_bounds
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (ν : (Fin n → ℝ) → ℝ) (hν : Continuous ν)
    {f : (Fin n → ℝ) → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R → ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X (continuousSublevelDomain ν hν R) I f g ∧
      MemLp g p (volume.restrict {x | ν x < R})) (A : ℝ)
    (hb : ∀ R : ℝ, 0 < R →
      weakWordENorm X (continuousSublevelDomain ν hν R) I p f ≤ ENNReal.ofReal A) :
    ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I f g ∧
      MemLp g p volume ∧ eLpNorm g p volume ≤ ENNReal.ofReal A := by
  apply exists_global_weakWord_of_scaleInvariant_local_bounds X I ν hν hp hpt hf hlocal A 0
  intro R hR
  simpa only [zero_mul, add_zero] using hb (R / 2) (by positivity)

end RothschildStein.H3
