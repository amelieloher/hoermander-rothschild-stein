-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import RothschildStein.S.ClassicalWords
public import RothschildStein.Definitions.hasWeakWordDeriv
public import RothschildStein.Definitions.wordBracket
public import RothschildStein.Definitions.wordWeight

/-!
# Kernel integrability, endpoint differentiation and transfer hypotheses

These propositions state the row and column integrability, differentiation at both endpoints, and
transfer to the integration variable used by the commutation, parametrix and representation
results. They are stated for a kernel
frame `F`, lifted fields
`Xt : Fin k → …` smooth on `V` with weights `w` (horizontal letters weight one, the drift letter
weight two; without drift there is no weight-two letter) and the chart's bracket basis `B`.
Those results take them as hypotheses; they are proved for the frames built from a `LiftedChart`
and its fundamental kernels.

Operator identities act on tests `f ∈ C_c^∞(V)`. A derivative of an output is the weak derivative
on `V` (`hasWeakWordDeriv`); a field applied to a test is the classical one, again a test
(`S.wordDerivativeTest`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

variable {N k : ℕ}

/-- Row and column integrability of positive-type kernels: the consequence of the growth
and shell bounds of the type calculus used to make positive-type operators linear on bounded inputs
(BB p. 544, Prop 11.10; p. 297, Lemma 7.5). -/
def TypeKernelIntegrable (F : KernelFrame N) : Prop :=
  ∀ lam : ℕ, 1 ≤ lam → ∀ kern : (Fin N → ℝ) → (Fin N → ℝ) → ℝ, IsTypeKernel F lam kern →
    ∀ ξ : Fin N → ℝ, Integrable (fun η => kern ξ η) ∧ Integrable (fun η => kern η ξ)

/-- Left differentiation: for type `lam ≥ w i`, `X̃ᵢ T` has type `lam - w i`; the weak
`X̃ᵢ`-derivative on `V` of `T f` is `S f` for every test `f` (BB pp. 546–551, Thm 11.15,
Lemmas 11.16, 11.18; with the drift degree corrected and both endpoint limits). -/
def LeftDifferentiation (F : KernelFrame N) (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) :
    Prop :=
  ∀ (lam : ℕ) (T : TypeOperator F lam) (i : Fin k), (w i : ℕ) ≤ lam →
    ∃ S : TypeOperator F (lam - w i), ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv Xt F.V [i] (T.apply f) (S.apply f)

/-- Right differentiation: for type `lam ≥ w i`, `T X̃ᵢ` has type `lam - w i`; on every
test `f`, `T (X̃ᵢ f) = S f` (BB p. 551, completion of Thm 11.15). -/
def RightDifferentiation (F : KernelFrame N) (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ))) : Prop :=
  ∀ (lam : ℕ) (T : TypeOperator F lam) (i : Fin k), (w i : ℕ) ≤ lam →
    ∃ S : TypeOperator F (lam - w i), ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      T.apply (RothschildStein.S.wordDerivativeTest F.V Xt hXt [i] f) = S.apply f

/-- Transfer to the integration variable: for type `lam ≥ w i` there are
`T_J` of type `lam + |J| - w i` (`J` a basis word with `|J| ≥ w i`) and `Tⁱ` of type
`lam + 1 - w i` with `X̃ᵢ T = ∑_J T_J X̃_[J] + Tⁱ` on tests. Horizontal letters give
types `lam + |J| - 1`, `lam`; the drift letter gives `|J| ≥ 2` and types
`lam + |J| - 2`, `lam - 1`) (BB pp. 552–559, Lemmas 11.21–11.23, Thm 11.24). -/
def DerivativeTransfer (F : KernelFrame N) (w : Fin k → ℕ+) (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (B : Fin N → List (Fin k)) : Prop :=
  ∀ (lam : ℕ) (T : TypeOperator F lam) (i : Fin k), (w i : ℕ) ≤ lam →
    ∃ (TJ : ∀ j : Fin N, TypeOperator F (lam + wordWeight w (B j) - w i))
      (T0 : TypeOperator F (lam + 1 - w i)),
      ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv Xt F.V [i] (T.apply f)
          (fun ξ => (∑ j ∈ Finset.univ.filter (fun j => (w i : ℕ) ≤ wordWeight w (B j)),
              (TJ j).apply (fieldDerivative (wordBracket Xt (B j)) f) ξ) + T0.apply f ξ)

end RothschildStein.P1
