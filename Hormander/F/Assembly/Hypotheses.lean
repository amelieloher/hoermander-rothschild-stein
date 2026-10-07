-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Coordinates
public import Hormander.F.DifferentialTransport
public import Hormander.F.SchwartzTransport
public import Hormander.F.FrameExtension
public import Hormander.Defs.HormanderOp
public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Hypotheses for the local regularity assembly

The local regularity estimate and localized forcing identity are explicit hypotheses of this
assembly, stated as `Prop`
valued definitions. A later proof of either one instantiates the corresponding definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap Topology Filter
open Hormander.Interface

namespace Hormander.F

/-- The localized input `χ u`, transported to the Euclidean carrier. -/
def localizedInput {N : ℕ} (χ : E₂ N → ℝ) (u : (Fin N → ℝ) → ℝ) : E₂ N → ℂ :=
  fun y => ((χ y * u ((coordinateEquiv N).symm y) : ℝ) : ℂ)

/-- The local regularity estimate used by the assembly. -/
def E4Statement : Prop :=
  ∀ {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (_hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (_hXc : ∀ i, HasCompactSupport (X i))
    (_hc : ContDiff ℝ (⊤ : ℕ∞) c) (_hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (_hK : IsCompact K) (_hU : IsOpen U) (_hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (_hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (_hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (_hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (_hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ))
        (Hormander.hormanderOp X c u) = (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (_hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u)),
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u)

/-- The localized forcing identity for a local patch: for `χ ∈ C_c^∞(B)` and
`η ∈ C_c^∞` with `χ = 1` near `tsupport η`, the input `χ u` is integrable and
`η L̃ (χ u) = η g` in `𝓢'`, with `η g` a Schwartz function. -/
def LocalizedForcingStatement {k N : ℕ} (hN : 0 < N) {Ω : Set (Fin N → ℝ)}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ) (x₀ : Fin N → ℝ)
    (P : LocalPatch hN (coordinateEquiv N '' Ω) (pushVectorFields X)
      (fun y => c ((coordinateEquiv N).symm y)) (coordinateEquiv N x₀)) : Prop :=
  ∀ (χ η : E₂ N → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
    tsupport χ ⊆ Metric.ball (coordinateEquiv N x₀) P.radius →
    ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    (∀ᶠ x in 𝓝ˢ (tsupport η), χ x = 1) →
    ∃ hv : Integrable (localizedInput χ u) volume, ∃ f : 𝓢(E₂ N, ℂ),
      (∀ y, f y = ((η y * g ((coordinateEquiv N).symm y) : ℝ) : ℂ)) ∧
      TemperedDistribution.smulLeftCLM ℂ (fun x => ((η x : ℝ) : ℂ))
        (Hormander.hormanderOp P.extendedX P.extendedC
          (Lp.toTemperedDistribution (hv.toL1 (localizedInput χ u)))) =
        (f : 𝓢'(E₂ N, ℂ))

end Hormander.F
