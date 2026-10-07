-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.LocalRegularity.MollifierConverse
public import Hormander.E.OneStepFinal.Main
public import Hormander.E.OneStepFinal.Final
public import Hormander.E.Iteration.Estimate

/-!
# One-step regularization with the mollifier converse

`Hormander.E.one_step_regularization_of_D1` with `hA6 := Hormander.A.mollifierConverse N`. The
remaining hypothesis is `D1Hypothesis`; applying the localized gain gives the one-step estimate.
-/

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution

namespace Hormander.E

/-- The one-step regularization estimate, assuming the localized gain statement; the mollifier
converse is instantiated. -/
theorem one_step_regularization_of_localized_gain (hD1 : D1Hypothesis) {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (η₁ η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ)
    (hη : Hormander.D.cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (r : ℝ) :
    ∃ C : ℝ, ∀ (u : 𝓢'(Hormander.B.Carrier N, ℂ))
      (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = Hormander.B.cutoffDistr η₂ u →
      b.toDistr = Hormander.B.cutoffDistr η₂ (Hormander.hormanderOp X c u) →
      ∃ v : Hormander.A.SobolevSpace N (r + (2 : ℝ) / 4 ^ s),
        v.toDistr = Hormander.B.cutoffDistr η₁ u ∧ ‖v‖ ≤ C * (‖b‖ + ‖a‖) :=
  one_step_regularization_of_D1 X c hX hXc hc hcc hK hU hKU s hs w hws hw η₁ η₂ hη hη₂K r
    (Hormander.A.mollifierConverse N) hD1

/-- The one-step hypothesis of the iteration at fixed frame data,
under the stated hypotheses. -/
theorem oneStepAtFixedFrame_of_localized_gain (hD1 : D1Hypothesis) {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x)) :
    OneStepAtFixedFrame X c hX hXc hc hcc hK hU hKU s hs w hws hw :=
  fun η₁ η₂ hη hη₂K r =>
    one_step_regularization_of_localized_gain hD1 X c hX hXc hc hcc hK hU hKU s hs w hws hw
      η₁ η₂ hη hη₂K r

end Hormander.E
