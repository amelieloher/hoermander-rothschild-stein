-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.TemperedDistribution

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace Hormander.B

abbrev Carrier (N : ℕ) := EuclideanSpace ℝ (Fin N)

abbrev TestFunction (N : ℕ) := SchwartzMap (Carrier N) ℂ

abbrev Tempered (N : ℕ) := TemperedDistribution (Carrier N) ℂ

abbrev Operator (N : ℕ) := TestFunction N →ₗ[ℂ] TestFunction N

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

noncomputable def sobolevSpace {N : ℕ} (s : ℝ) (u : TestFunction N) :
    BesselPotentialSpace (Carrier N) ℂ s 2 :=
  (SchwartzMap.memSobolev (s := s) (p := 2) u).toBesselPotentialSpace

noncomputable def sobolevNorm {N : ℕ} (s : ℝ) (u : TestFunction N) : ℝ :=
  ‖sobolevSpace s u‖

/-- The order predicate on complex-linear operators on Schwartz functions. -/
def HasOrder {N : ℕ} (m : ℝ) (T : Operator N) : Prop :=
  ∀ s : ℝ, ∃ C : NNReal, ∀ u : TestFunction N,
    sobolevNorm s (T u) ≤ (C : ℝ) * sobolevNorm (s + m) u

/-- The Fourier-defined Bessel multiplier on Schwartz functions. -/
def lambdaOperator {N : ℕ} (s : ℝ) : Operator N :=
  (SchwartzMap.fourierMultiplierCLM ℂ
    (fun ξ : Carrier N => Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ (s / 2)))).toLinearMap

/-- The bilinear integral pairing used to define transposes on Schwartz functions. -/
def bilinearPairing {N : ℕ} (u v : TestFunction N) : ℂ :=
  ∫ x, u x * v x

/-- The algebraic identity that makes `Tt` the bilinear transpose of `T`. -/
def HasBilinearTranspose {N : ℕ} (T Tt : Operator N) : Prop :=
  ∀ u v : TestFunction N, bilinearPairing (T u) v = bilinearPairing u (Tt v)

/-- A real Schwartz vector field in coordinate form on the Euclidean carrier. -/
abbrev RealSchwartzVectorField (N : ℕ) := Fin N → SchwartzMap (Carrier N) ℝ

/-- The Schwartz multiplier associated to a complex Schwartz coefficient. -/
def multiplierOperator {N : ℕ} (g : SchwartzMap (Carrier N) ℂ) : Operator N :=
  (SchwartzMap.smulLeftCLM ℂ g).toLinearMap

/-- Complexify a real Schwartz coefficient while retaining its Schwartz structure. -/
def complexifyRealSchwartz {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) :
    SchwartzMap (Carrier N) ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM g

/-- Multiplication by a real Schwartz coefficient on complex-valued Schwartz functions. -/
def realMultiplierOperator {N : ℕ} (g : SchwartzMap (Carrier N) ℝ) : Operator N :=
  multiplierOperator (complexifyRealSchwartz g)

/-- A coordinate directional derivative on Schwartz functions. -/
def coordinateDerivative {N : ℕ} (i : Fin N) : Operator N :=
  (LineDeriv.lineDerivOpCLM ℂ (TestFunction N)
    (EuclideanSpace.single i (1 : ℝ))).toLinearMap

/-- The differential operator of a real Schwartz vector field on Schwartz functions. -/
def vectorFieldOperator {N : ℕ} (V : RealSchwartzVectorField N) : Operator N :=
  ∑ i : Fin N, (realMultiplierOperator (V i)).comp (coordinateDerivative i)

/-- A generator used in the iterated-commutator definition of the order classes. -/
inductive OperatorGenerator (N : ℕ) where
  | vectorField : RealSchwartzVectorField N → OperatorGenerator N
  | multiplier : SchwartzMap (Carrier N) ℝ → OperatorGenerator N

/-- The Schwartz operator attached to a real vector field or real multiplier. -/
def OperatorGenerator.toOperator {N : ℕ} : OperatorGenerator N → Operator N
  | .vectorField V => vectorFieldOperator V
  | .multiplier g => realMultiplierOperator g

/-- Whether an order generator is a multiplier. -/
def OperatorGenerator.isMultiplier {N : ℕ} : OperatorGenerator N → Bool
  | .vectorField _ => false
  | .multiplier _ => true

/-- The commutator convention `[A,B]=A∘B−B∘A` on Schwartz operators. -/
def operatorComm {N : ℕ} (A B : Operator N) : Operator N :=
  A.comp B - B.comp A

/-- The iterated commutator `ad Y₁ … ad Yᵣ T`, with the first list entry outermost. -/
def iteratedCommutator {N : ℕ} : List (OperatorGenerator N) → Operator N → Operator N
  | [], T => T
  | Y :: Ys, T => operatorComm Y.toOperator (iteratedCommutator Ys T)

/-- Count the multiplier entries in an iterated-commutator word. -/
def multiplierCount {N : ℕ} (ys : List (OperatorGenerator N)) : ℕ :=
  (ys.filter OperatorGenerator.isMultiplier).length

/-- The commutator-order class `𝓞^m`, including a bilinear transpose witness. -/
def OperatorClass {N : ℕ} (m : ℝ) (T : Operator N) : Prop :=
  ∃ Tt : Operator N, HasBilinearTranspose T Tt ∧
    ∀ ys : List (OperatorGenerator N),
      HasOrder (m - (multiplierCount ys : ℝ)) (iteratedCommutator ys T)

/-- Extend an operator to tempered distributions by precomposition with its transpose. -/
def transposeExtension {N : ℕ}
    (Tt : TestFunction N →L[ℂ] TestFunction N) : Tempered N →L[ℂ] Tempered N :=
  PointwiseConvergenceCLM.precomp ℂ Tt

@[simp]
theorem transposeExtension_apply_apply {N : ℕ}
    (Tt : TestFunction N →L[ℂ] TestFunction N) (u : Tempered N) (φ : TestFunction N) :
    transposeExtension Tt u φ = u (Tt φ) := rfl

end Hormander.B
