-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.fieldDerivative
public import HeatKernel.Definitions.horizontalL2Distance
public import HeatKernel.Provider.horizontal_poincare

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HeatKernel

open RothschildStein

/-- Same-ball horizontal Poincaré inequality on a Carnot group (Jerison 1986, Theorem 2.1): for
every `1 ≤ p < ∞` there is `C` such that for every open ball `B = B(x, r)` of the horizontal
`ℓ²`-control distance `horizontalL2Distance X` and every `u` that is `C¹` on a neighbourhood of the
closure of `B`, `(⨍_B |u - u_B|^p)^{1/p} ≤ C r (⨍_B |Xu|^p)^{1/p}`, where `|Xu|` is the Euclidean
norm of the horizontal gradient `(X₁ u, …, X_q u)`. -/
theorem horizontal_poincare
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (p : ℝ) (hp : 1 ≤ p) :
    let X := G.horizontalFields hq
    let B : (Fin N → ℝ) → ℝ → Set (Fin N → ℝ) :=
      fun x r => {y | horizontalL2Distance X x y < ENNReal.ofReal r}
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (u : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ)),
        IsOpen U → closure (B x r) ⊆ U → ContDiffOn ℝ 1 u U →
        (⨍ y in B x r, |u y - ⨍ z in B x r, u z| ^ p) ^ (1 / p) ≤
          C * r * (⨍ y in B x r, Real.sqrt (∑ i, fieldDerivative (X i) u y ^ 2) ^ p) ^ (1 / p) :=
  by exact HeatKernel.Provider.horizontal_poincare G hq hqpos hw hspan p hp

end HeatKernel
