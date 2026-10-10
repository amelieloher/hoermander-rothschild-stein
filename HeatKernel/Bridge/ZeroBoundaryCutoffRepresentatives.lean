-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryCurves
public import HeatKernel.Form.EssentialSupportZeroBoundary
import Mathlib.Tactic.Linter

/-! # Zero-boundary representatives of compact cutoff energy curves -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- An energy curve represented by a compact cutoff has a zero-boundary
representative with exactly the same ambient value-gradient pair. -/
theorem exists_zeroBoundary_cutoff_curve {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : T → energyGraph (N := N) ⊤ X) (hv : MemLp v 2 μ)
    {u : T → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (V : Set (Fin N → ℝ)))
    (hrep : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x) :
    ∃ w : T → zeroBoundaryGraph V X, MemLp w 2 μ ∧
      ∀ᵐ t ∂μ, (w t : GradientSpace (N := N) ⊤ q) = (v t : GradientSpace (N := N) ⊤ q) := by
  apply exists_zeroBoundaryGraph_curve_of_ae_mem V X v hv
  filter_upwards [hrep] with t ht
  apply mem_zeroBoundaryGraph_of_ae_zero_off_compact V X hX (v t) hc hs
  filter_upwards [ht] with x hx hn
  rw [hx, image_eq_zero_of_notMem_tsupport hn, mul_zero]

end HeatKernel
