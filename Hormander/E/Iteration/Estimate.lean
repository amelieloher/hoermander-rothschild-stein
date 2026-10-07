-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.Iteration.Uniform

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution
open Hormander.B
open Hormander.Interface

namespace Hormander.E

/-- The distributional finite-iteration estimate (BB Theorem 5.64) in the interface
style: a constant `C`, chosen from the frame data, the cutoffs and the orders `m`, `σ` before any
distribution is given, such that localized data `ζ' u ∈ H^{-m}` and `ζ' L̃ u ∈ H^σ` give
`ζ u ∈ H^{σ + 2 / 4 ^ s}` with `‖ζ u‖ ≤ C (‖ζ' L̃ u‖ + ‖ζ' u‖)`, assuming the one-step
estimate at the fixed frame data. -/
theorem distributional_estimate_of_one_step {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (Carrier N)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (s : ℕ) (hs : 1 ≤ s) (w : Fin N → LieWord k)
    (hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (hE2 : OneStepAtFixedFrame X c hX hXc hc hcc hK hU hKU s hs w hws hw)
    (ζ ζ' : SchwartzMap (Carrier N) ℝ)
    (hζ : Hormander.D.cutoffPrecedes (ζ : Carrier N → ℝ) (ζ' : Carrier N → ℝ))
    (hζ'K : tsupport (ζ' : Carrier N → ℝ) ⊆ K)
    {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) :
    ∃ C : ℝ, ∀ (u : 𝓢'(Carrier N, ℂ)) (a : Hormander.A.SobolevSpace N (-m))
      (b : Hormander.A.SobolevSpace N σ),
      a.toDistr = Hormander.B.cutoffDistr ζ' u →
      b.toDistr = Hormander.B.cutoffDistr ζ' (Hormander.hormanderOp X c u) →
      ∃ v : Hormander.A.SobolevSpace N (σ + (2 : ℝ) / 4 ^ s),
        v.toDistr = Hormander.B.cutoffDistr ζ u ∧ ‖v‖ ≤ C * (‖b‖ + ‖a‖) := by
  obtain ⟨C, hC⟩ := finite_iteration_estimate_uniform_of_one_step
    X c hX hXc hc hcc hK hU hKU s hs w hws hw hE2 hζ hζ'K hm hσ
  refine ⟨C, fun u a b ha hb => ?_⟩
  have houter : ∀ x, ζ' x = Hormander.B.cutoffSchwartzOuter hζ x := fun x => rfl
  have hinner : ∀ x, Hormander.B.cutoffSchwartz hζ x = ζ x := fun x => rfl
  obtain ⟨v, hv, hvnorm⟩ := hC u a b
    (ha.trans (cutoffDistr_congr houter u))
    (hb.trans (cutoffDistr_congr houter (Hormander.hormanderOp X c u)))
  exact ⟨v, hv.trans (cutoffDistr_congr hinner u), hvnorm⟩

end Hormander.E

end
