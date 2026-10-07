-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordEval
public import Hormander.Defs.HormanderOp
public import Mathlib.Analysis.Distribution.Sobolev
public import Hormander.Provider.LocalRegularity

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap Topology Filter
open Hormander.Interface

namespace Hormander

/-- BB Thm. 5.64, in corrected form: for `L = Σ_{i=1}^k Xᵢ² + X₀ + c` with real `C_c^∞`
coefficients and `N` Lie words giving a basis at every point of an open neighbourhood `U` of a
compact `K`, let `ζ, ζ'` be real smooth cut-offs with `ζ' = 1` near `tsupport ζ` and
`tsupport ζ' ⊆ K`. If `u ∈ 𝓢'`, `ζ' L u` is a Schwartz function and `ζ' u ∈ H^{-m}`, then
`ζ u ∈ H^t` for every `t`. -/
theorem forall_memSobolev_of_localized {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (EuclideanSpace ℝ (Fin N))} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => lieWordEval X (w a) x))
    {ζ ζ' : EuclideanSpace ℝ (Fin N) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (u : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)) (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ))
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) (hormanderOp X c u) =
      (f : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)))
    {m : ℝ}
    (hm : TemperedDistribution.MemSobolev (-m) 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ' x : ℝ) : ℂ)) u)) :
    ∀ t : ℝ, TemperedDistribution.MemSobolev t 2
      (TemperedDistribution.smulLeftCLM ℂ (fun x => ((ζ x : ℝ) : ℂ)) u) :=
  by exact Hormander.Provider.forall_memSobolev_of_localized X c hX hXc hc hcc hK hU hKU w hw hζ hζ' hζζ' hζ'K u f hf hm

end Hormander
