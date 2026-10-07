-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.LieAlgebraSpansOn
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal


@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace RothschildStein

def testMultiplierOn {n : ℕ} (Ω : Opens (Fin n → ℝ))
    (a : (Fin n → ℝ) → ℝ)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) := by
  refine ⟨fun x => φ x * a x, ?_, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · exact φ.contDiff.contDiffAt.mul (ha.contDiffAt (Ω.isOpen.mem_nhds hx))
    · have hxs : x ∉ tsupport (φ : (Fin n → ℝ) → ℝ) :=
        fun h => hx (φ.tsupport_subset h)
      have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport (φ : (Fin n → ℝ) → ℝ) :=
        isClosed_closure.isOpen_compl.mem_nhds hxs
      exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun _ : Fin n → ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
          (he.mono fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
  · exact φ.hasCompactSupport.mul_right
  · exact tsupport_mul_subset_left.trans φ.tsupport_subset

end RothschildStein
