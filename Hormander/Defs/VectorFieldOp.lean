-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

noncomputable section

open SchwartzMap

namespace Hormander

/-- The first-order operator `Σᵢ Vⁱ ∂ᵢ` of a vector field `V` on `ℝᴺ`, acting on complex tempered
distributions: `∂ᵢ` is Mathlib's distributional directional derivative along the `i`-th unit
vector and `Vⁱ` acts by `TemperedDistribution.smulLeftCLM`. This is the action of `V` on `𝓢'`
for every `V` whose coordinates have temperate growth (in particular for `C_c^∞` fields, the
only case used). -/
def vectorFieldOp {N : ℕ} (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    𝓢'(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin N), ℂ) :=
  ∑ i : Fin N,
    (TemperedDistribution.smulLeftCLM ℂ (fun x => ((V x i : ℝ) : ℂ))).comp
      (LineDeriv.lineDerivOpCLM ℂ 𝓢'(EuclideanSpace ℝ (Fin N), ℂ)
        (EuclideanSpace.single i (1 : ℝ)))

end Hormander
