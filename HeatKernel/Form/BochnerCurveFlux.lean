-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.TimeDependentMultiplication
public import HeatKernel.Form.BoundedCoefficientSlices
public import HeatKernel.Form.GradientCurves
import Mathlib.Tactic.Linter

/-! # Matrix fluxes of Bochner spatial L² curves -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal

namespace HeatKernel

/-- A bounded jointly measurable matrix field acts on a Bochner L² vector curve to produce a
Bochner L² flux with the expected spatial representatives. No joint representative of the input
curve is needed as a premise. -/
theorem exists_Bochner_flux_of_L2_curve {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {N q : ℕ} (U : Opens (Fin N → ℝ))
    (a : Fin q → Fin q → T × (Fin N → ℝ) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i j, AEStronglyMeasurable (a i j)
      (μ.prod (volume.restrict (U : Set (Fin N → ℝ)))))
    (hb : ∀ i j, ∀ᵐ z ∂μ.prod (volume.restrict (U : Set (Fin N → ℝ))), ‖a i j z‖ ≤ C)
    (v : T → PiLp 2 (fun _ : Fin q => SpatialL2 U)) (hv : MemLp v 2 μ) :
    ∃ J : T → PiLp 2 (fun _ : Fin q => SpatialL2 U), MemLp J 2 μ ∧
      ∀ i, ∀ᵐ t ∂μ, J t i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
        fun x => ∑ j, a i j (t, x) * v t j x := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : IsSeparable (volume.restrict (U : Set (Fin N → ℝ))) := isSeparable_of_sigmaFinite _
  obtain ⟨a', ha', hs, he⟩ := exists_bounded_measurable_total_slices a hC ha hb
  have hvcomp : ∀ j, MemLp (fun t => v t j) 2 μ := by
    rw [← memLp_comp_continuousLinearEquiv_iff
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => SpatialL2 U)) v, memLp_pi_iff] at hv
    exact hv
  let f : Fin q → Fin q → T → SpatialL2 U := fun i j t =>
    boundedL2Mul (hs t i j).1 hC (hs t i j).2 (v t j)
  have hf : ∀ i j, MemLp (f i j) 2 μ := by
    intro i j
    exact memLp_boundedL2Mul_curve (a := fun t x => a' i j (t, x)) hC
      (by simpa only [Function.uncurry_def] using ha' i j) (fun t => (hs t i j).1)
      (fun t => (hs t i j).2) (hvcomp j)
  let J : T → PiLp 2 (fun _ : Fin q => SpatialL2 U) :=
    fun t => WithLp.toLp 2 (fun i => ∑ j, f i j t)
  refine ⟨J, ?_, fun i => ?_⟩
  · rw [← memLp_comp_continuousLinearEquiv_iff
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin q => SpatialL2 U)) J, memLp_pi_iff]
    intro i
    change MemLp (fun t => ∑ j, f i j t) 2 μ
    simpa only [Finset.sum_apply] using
      memLp_finsetSum Finset.univ (fun j _ => hf i j)
  · filter_upwards [he] with t ht
    have H : (∑ j, f i j t : SpatialL2 U) =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
        fun x => ∑ j, f i j t x := Lp.coeFn_fun_finsetSum Finset.univ (fun j => f i j t)
    have Hf : ∀ j, f i j t =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
        fun x => a' i j (t, x) * v t j x := fun j =>
      boundedL2Mul_ae (hs t i j).1 hC (hs t i j).2 (v t j)
    change (∑ j, f i j t : SpatialL2 U) =ᵐ[_] _
    filter_upwards [H, ae_all_iff.mpr Hf] with x hx hfx
    rw [hx]
    exact Finset.sum_congr rfl fun j _ => (hfx j).trans (by rw [ht i j x])



end HeatKernel
