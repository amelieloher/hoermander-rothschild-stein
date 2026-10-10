-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicReciprocalTest
public import HeatKernel.Moser.WeakSolutionSpatialWeights
import all Mathlib.Basic.Real.Basic

/-! # Literal representatives of spatially weighted reciprocal tests -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- The centered reciprocal test has the reciprocal-square derivative on positive inputs. -/
theorem hasDerivAt_shiftedReciprocalWeakSolutionTest {c s : ℝ}
    (hc : 0 < c) (hs : 0 < s) :
    HasDerivAt (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)).toFun
      (-((s + c) ^ 2)⁻¹) s := by
  have hd := ((hasDerivAt_inv (add_pos hs hc).ne').comp s
    ((hasDerivAt_id s).add_const c)).sub_const c⁻¹
  have hd' : HasDerivAt (fun t : ℝ => (t + c)⁻¹ - c⁻¹) (-((s + c) ^ 2)⁻¹) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact shiftedReciprocalWeakSolutionTest_eq hc ht.le

/-- The weighted reciprocal test retains both the reciprocal-square chain term and
 the full weight-gradient term on nonnegative energy representatives, including zero levels. -/
theorem WeakSolutionSpatialWeight.reciprocal_energyMap_gradient_ae {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c : ℝ} (hc : 0 < c) (z : zeroBoundaryGraph V X) (i : Fin q)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    ∀ᵐ x ∂volume,
      (W.energyMap hX (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) z :
        GradientSpace (N := N) ⊤ q).snd i x =
      W.toFun x * (-(((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ 2)⁻¹ *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
      W.gradient i x * (((z : GradientSpace (N := N) ⊤ q).fst x + c)⁻¹ - c⁻¹) := by
  filter_upwards [W.energyMap_gradient_ae hX
    (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)) z i, hz,
    energyGraph_gradient_zero_on_level X hX (zeroBoundaryEnergyInclusion V X z) 0 i]
    with x hx hnonneg hzero
  by_cases hs : 0 < (z : GradientSpace (N := N) ⊤ q).fst x
  · rw [hx, (hasDerivAt_shiftedReciprocalWeakSolutionTest hc hs).deriv,
      shiftedReciprocalWeakSolutionTest_eq hc hs.le]
  · have heq : (z : GradientSpace (N := N) ⊤ q).fst x = 0 :=
      le_antisymm (le_of_not_gt hs) hnonneg
    have hg : (z : GradientSpace (N := N) ⊤ q).snd i x = 0 := hzero heq
    rw [hx, hg, heq, shiftedReciprocalWeakSolutionTest_eq hc (le_refl 0)]
    simp

end HeatKernel
