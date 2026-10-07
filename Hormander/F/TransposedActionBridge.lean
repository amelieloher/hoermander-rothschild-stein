-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.HormanderOp
public import Hormander.F.Transpose
public import Hormander.C.C9Bridges
public import Hormander.C.Energy.Estimate
public import Hormander.B.Extension.Continuity
public import Hormander.B.Nested.RealDiffOps
public import Hormander.E.OneStep.ExtAlgebra
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution
open Hormander.B
open MeasureTheory
open scoped BigOperators

namespace Hormander.F

/-- Testing a first-order distributional field action applies the negative derivative after
multiplication by the corresponding coefficient. -/
theorem vectorFieldOp_apply_as_transpose_sum {N : ℕ}
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) :
    Hormander.vectorFieldOp V T φ =
      ∑ i : Fin N, T
        (-(LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin N), ℂ)
          (EuclideanSpace.single i (1 : ℝ)))
          (SchwartzMap.smulLeftCLM ℂ
            (fun x => ((V x i : ℝ) : ℂ)) φ)) := by
  classical
  rw [Hormander.vectorFieldOp]
  rw [_root_.sum_apply]
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply,
    TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.lineDerivOpCLM_eq]
  rfl

/-- The algebraic transpose on Schwartz tests of the vector-field operator. -/
def vectorFieldTransposeSchwartz {N : ℕ}
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) :
    𝓢(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin N), ℂ) :=
  ∑ i : Fin N,
    (-(LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ (Fin N), ℂ)
      (EuclideanSpace.single i (1 : ℝ)))).comp
      (SchwartzMap.smulLeftCLM ℂ (fun x => ((V x i : ℝ) : ℂ)))

/-- The first-order distribution action evaluates by its
algebraic transpose. -/
theorem vectorFieldOp_apply_transpose {N : ℕ}
    (V : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) :
    Hormander.vectorFieldOp V T φ = T (vectorFieldTransposeSchwartz V φ) := by
  rw [vectorFieldOp_apply_as_transpose_sum]
  simp [vectorFieldTransposeSchwartz, map_sum]

/-- The Schwartz-test transpose associated with the sum-of-squares operator. -/
def hormanderTransposeSchwartz {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ) :
    𝓢(EuclideanSpace ℝ (Fin N), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin N), ℂ) :=
  (∑ i : Fin k,
      (vectorFieldTransposeSchwartz (X i.succ)).comp
        (vectorFieldTransposeSchwartz (X i.succ))) +
    vectorFieldTransposeSchwartz (X 0) +
    SchwartzMap.smulLeftCLM ℂ (fun x => ((c x : ℝ) : ℂ))

/-- The Hörmander operator on tempered distributions is the transpose action of the
Schwartz-test operator assembled from its first-order terms. -/
theorem hormanderOp_apply_transpose {k N : ℕ}
    (X : Fin (k + 1) → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (c : EuclideanSpace ℝ (Fin N) → ℝ)
    (T : 𝓢'(EuclideanSpace ℝ (Fin N), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) :
    Hormander.hormanderOp X c T φ = T (hormanderTransposeSchwartz X c φ) := by
  simp [Hormander.hormanderOp, hormanderTransposeSchwartz,
    vectorFieldOp_apply_transpose, map_add, map_sum,
    ContinuousLinearMap.comp_apply]

end Hormander.F
