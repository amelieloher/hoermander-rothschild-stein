-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Assembly.Estimate
public import Hormander.C.C9Bridges

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform

namespace Hormander.C

open Hormander.B

/-- The basic subelliptic estimate follows from the closure facts, the horizontal recurrence for
the Schwartz representatives of the fields, and the frame coordinate inequality. -/
theorem subelliptic_estimate_of_facts {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    (F : B10Facts N) (hH : HorizontalRecurrence (c9SchwartzVectorField X hX hXc))
    (hCoord : CoordinateInequality N)
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
  subelliptic_estimate_of_inputs X c hX (c9SchwartzVectorField X hX hXc) (fun _ _ _ => rfl)
    (c9SchwartzMultiplier c hc hcc) (fun _ => rfl) F hH hCoord hK hU hKU s hs w hws hw

end Hormander.C
