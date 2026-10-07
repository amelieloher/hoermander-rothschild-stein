-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Assembly.Final

/-!
# Basic subelliptic estimate

This module proves the basic subelliptic estimate from the Section C assembly.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform

namespace Hormander.Provider

/-- The basic subelliptic estimate with gain `ε = 2/4^s`. -/
theorem subelliptic_estimate {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x)) :
    ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ), tsupport u ⊆ K →
      (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑u) ξ‖ ^ 2) ≤
        C * ((∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) +
            ∫ x, ‖u x‖ ^ 2) :=
  Hormander.C.subelliptic_estimate_unconditional X c hX hXc hc hcc hK hU hKU s hs w hws hw

end Hormander.Provider
