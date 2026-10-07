-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CommutatorPairProperties
public import RothschildStein.S.SmoothKernelTransferMean
public import RothschildStein.S.SmoothFriedrichsBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.S
variable {n q : ℕ}

/-- The actual recursive kernels built from the base mollifier and
smooth vector-field transfers (BB (2.10)–(2.12), pp. 77–79). -/
def smoothFriedrichsCommutatorPairs
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (X j)) (I : List (Fin q)) :
    List (SmoothFriedrichsKernel n × List (Fin q)) :=
  friedrichsCommutatorPairs
    (fun j => smoothKernelTransfer (smoothBaseFriedrichsKernel n) (X j) (hX j))
    (fun j K => smoothKernelTransfer K (X j) (hX j)) I

/-- Every actual recursive commutator kernel has integral zero
for all x,ε; no mean-cancellation hypothesis is left to callers
(BB properties (a),(b), pp. 76–79). -/
theorem smoothFriedrichsCommutatorPairs_mean_zero
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (X j)) (I : List (Fin q))
    {p : SmoothFriedrichsKernel n × List (Fin q)}
    (hp : p ∈ smoothFriedrichsCommutatorPairs X hX I) (ε : ℝ) (x : Fin n → ℝ) :
    (∫ y, p.1.family ε x y) = 0 := by
  have H := friedrichsCommutatorPairs_kernel_property
    (fun j => smoothKernelTransfer (smoothBaseFriedrichsKernel n) (X j) (hX j))
    (fun j K => smoothKernelTransfer K (X j) (hX j))
    (fun K => ∀ ε x, (∫ y, K.family ε x y) = 0)
    (by
      intro j ε x
      exact smoothKernelTransfer_mean_zero_of_constant_mean
        (smoothBaseFriedrichsKernel n) (X j) (hX j) isOpen_univ ε 1
        (fun z _ => smoothBaseFriedrichsKernel_mean ε z) (mem_univ x))
    (by
      intro j K hK ε x
      exact smoothKernelTransfer_mean_zero_of_constant_mean K (X j) (hX j)
        isOpen_univ ε 0 (fun z _ => hK ε z) (mem_univ x)) I hp
  exact H ε x

/-- On every compact open patch, each constructed pair exports the
exact bounded, vanishing-mean certificate required by (BB pp. 76–79). -/
theorem smoothFriedrichsCommutatorPairs_hasVanishingMean
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (X j)) (I : List (Fin q))
    {p : SmoothFriedrichsKernel n × List (Fin q)}
    (hp : p ∈ smoothFriedrichsCommutatorPairs X hX I)
    (U : Set (Fin n → ℝ)) (hU : IsCompact (closure U)) (δ : ℝ) :
    HasVanishingKernelMean (p.1.toBounded U hU δ) := by
  intro ε _ x _
  exact smoothFriedrichsCommutatorPairs_mean_zero X hX I hp ε x

end RothschildStein.S
