-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.SmoothRepresentative.Main
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Smooth representative from all Sobolev orders

Every tempered distribution that belongs to all Sobolev spaces has a smooth representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.Provider

/-- A tempered distribution on `ℝᴺ` lying in every Sobolev space `H^s` is represented
by a smooth function. -/
theorem exists_contDiff_of_forall_memSobolev {N : ℕ}
    {T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)}
    (hT : ∀ s : ℝ, TemperedDistribution.MemSobolev s 2 T) :
    ∃ f : EuclideanSpace ℝ (Fin N) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ),
          Integrable (fun x => φ x * f x) ∧ T φ = ∫ x, φ x * f x :=
  Hormander.A.exists_contDiff_of_forall_memSobolev hT

end Hormander.Provider
