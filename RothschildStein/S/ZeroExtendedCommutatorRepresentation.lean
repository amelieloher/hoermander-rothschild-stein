-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CommutatorRepresentationGerms
public import RothschildStein.S.BaseKernelAllDimensions
public import RothschildStein.S.KernelZeroExtension
public import RothschildStein.S.WordDerivativeGerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- The local commutator representation applies exactly to
zero-extended ordinary mollification, including its classical words.
Equality on the open interior patch supplies the required derivative
germs (BB Thm 2.9, p. 73; domain). -/
theorem zeroExtended_commutator_representation
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (B : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hB : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (B j))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hG : ∀ j z, z ∈ cthickening δ (closure U) → B j =ᶠ[𝓝 z] X j)
    (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J, J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    {x : Fin n → ℝ} (hx : x ∈ U) :
    wordDerivative X I (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) x -
      euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator (jet I)) ε x =
      ((smoothFriedrichsCommutatorPairs B hB I).map
        (fun p => friedrichsKernelOp p.1.family (jet p.2) ε x)).sum := by
  have he (g : (Fin n → ℝ) → ℝ) (a : Fin n → ℝ) (ha : a ∈ U) :
      euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator g) ε a =
        euclideanRegularize n g ε a := by
    rw [← smoothBaseFriedrichsKernel_op _ hε.1,← smoothBaseFriedrichsKernel_op g hε.1]
    exact (smoothFriedrichsKernelOp_eq_zeroExtension Ω (smoothBaseFriedrichsKernel n) g hε.1 a
      ((closedBall_subset_closedBall hε.2.le).trans
        (closedBall_subset_of_interior_thickening Ω hδ ha))).symm
  have hg : euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε =ᶠ[𝓝 x]
      euclideanRegularize n f ε := by
    filter_upwards [hU.mem_nhds hx] with a ha
    exact he f a ha
  rw [(wordDerivative_eventuallyEq X I hg).eq_of_nhds,he (jet I) x hx]
  have H := smoothFriedrichsCommutatorPairs_representation_of_coefficient_germs
    Ω X hX B hB hU hc hε hδ hG I f jet hzero hw hx
  rw [smoothBaseFriedrichsKernel_op f hε.1,smoothBaseFriedrichsKernel_op (jet I) hε.1] at H
  linarith

end RothschildStein.S
