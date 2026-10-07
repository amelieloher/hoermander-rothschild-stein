-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordLength
public import Hormander.Defs.LieWordEval
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Hormander.Provider.SubellipticEstimate

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open Hormander.Interface

namespace Hormander

/-- The basic subelliptic estimate (BB Thm. 5.54, with the ordinary word length),
with gain `ε = 2/4^s` for `L = Σ_{i=1}^k Xᵢ² + X₀ + c` with real `C_c^∞` coefficients, on
Schwartz functions supported in a compact set `K`, when `N` Lie words of length at most `s` give
a basis at every point of an open neighbourhood `U` of `K`. In squared form:
`‖u‖²_{H^ε} = ∫ (1 + ‖ξ‖²)^ε |û(ξ)|² dξ ≤ C (‖Lu‖²_{L²} + ‖u‖²_{L²})`, where
`Xu(x) = Du(x)[X(x)]`. -/
theorem subelliptic_estimate {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → LieWord k) (hws : ∀ a, lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x)) :
    ∃ C : ℝ, ∀ u : 𝓢(EuclideanSpace ℝ (Fin N), ℂ), tsupport u ⊆ K →
      (∫ ξ, (1 + ‖ξ‖ ^ 2) ^ ((2 : ℝ) / 4 ^ s) * ‖𝓕 (⇑u) ξ‖ ^ 2) ≤
        C * ((∫ x, ‖(∑ i : Fin k,
                fderiv ℝ (fun y => fderiv ℝ u y (X i.succ y)) x (X i.succ x)) +
              fderiv ℝ u x (X 0 x) + (c x : ℂ) * u x‖ ^ 2) +
            ∫ x, ‖u x‖ ^ 2) :=
  by exact Hormander.Provider.subelliptic_estimate X c hX hXc hc hcc hK hU hKU s hs w hws hw

end Hormander
