-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierKernel
public import RothschildStein.S.CompactKernelIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The bounded Friedrichs kernel class: smoothness in (x,y), unit
coordinate-ball support in y, and uniform finite-order joint jets for 0<ε<δ
(BB properties (a),(b), p. 76). -/
structure BoundedFriedrichsKernel (U : Set (Fin n → ℝ)) (δ : ℝ) where
  toFun : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  smooth : ∀ ε ∈ Ioo 0 δ, ContDiffOn ℝ (⊤ : ℕ∞) (uncurry (toFun ε)) (U ×ˢ univ)
  support : ∀ ε ∈ Ioo 0 δ, ∀ x ∈ U,
    Function.support (toFun ε x) ⊆ closedBall 0 1
  jetBound : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo 0 δ,
    ∀ p ∈ U ×ˢ univ, ‖iteratedFDeriv ℝ m (uncurry (toFun ε)) p‖ ≤ C

/-- The vanishing-mean subclass, with the exact zero integral
required in the Friedrichs approximation estimate (BB Lemma 2.11, p. 74). -/
def HasVanishingKernelMean {U : Set (Fin n → ℝ)} {δ : ℝ}
    (K : BoundedFriedrichsKernel U δ) : Prop :=
  ∀ ε ∈ Ioo 0 δ, ∀ x ∈ U, (∫ y, K.toFun ε x y) = 0

/-- The fixed-coordinate kernel operator on total representatives
(BB (2.8),(2.11), pp. 75–78). -/
def friedrichsKernelOp (K : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (h : (Fin n → ℝ) → ℝ) (ε : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, K ε x y * h (x+ε • y)

/-- Rescaling a kernel to the integration-variable coordinates
(BB (2.11), p. 78; weak transfer). -/
def friedrichsRescaledKernel
    (K : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (ε : ℝ) (x z : Fin n → ℝ) : ℝ :=
  (ε^n)⁻¹ * K ε x (ε⁻¹ • (z-x))

/-- Kernel sections are smooth on the whole y-space at every
admissible x (BB p. 76). -/
theorem BoundedFriedrichsKernel.section_smooth {U : Set (Fin n → ℝ)} {δ : ℝ}
    (K : BoundedFriedrichsKernel U δ) {ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ U) : ContDiff ℝ (⊤ : ℕ∞) (K.toFun ε x) := by
  rw [← contDiffOn_univ]
  exact (K.smooth ε hε).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun y _ => ⟨hx,mem_univ y⟩)

/-- Every y-section has compact support in the closed unit ball
(BB p. 76). -/
theorem BoundedFriedrichsKernel.section_compact {U : Set (Fin n → ℝ)} {δ : ℝ}
    (K : BoundedFriedrichsKernel U δ) {ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ U) : HasCompactSupport (K.toFun ε x) :=
  (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset isClosed_closure
    (closure_minimal (K.support ε hε x hx) isClosed_closedBall)

/-- Smooth compact sections are integrable, so the zero-mean
condition refers to an actual integral (BB Lemma 2.11, p. 74). -/
theorem BoundedFriedrichsKernel.section_integrable {U : Set (Fin n → ℝ)} {δ : ℝ}
    (K : BoundedFriedrichsKernel U δ) {ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ U) : Integrable (K.toFun ε x) volume :=
  (K.section_smooth hε hx).continuous.integrable_of_hasCompactSupport
    (K.section_compact hε hx)

end RothschildStein.S
