-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionSpatialWeights
public import HeatKernel.Sobolev.GradientRepresentativeMoments
import Mathlib.Tactic

/-! # Quadratic energy of the spatially cut off half-power -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Multiplication by a unit cutoff bounds its value energy by the original energy. Its complete
horizontal product gradient is controlled by twice the localized original gradient
energy and twice the squared cutoff-gradient bound times the value energy. -/
theorem WeakSolutionSpatialWeight.cutoff_quadratic_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X)
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ} {L : ℝ}
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1)
    (hW : W.toFun =ᵐ[volume] η) (hWd : ∀ i, W.gradient i =ᵐ[volume] d i)
    (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (z : zeroBoundaryGraph V X) :
    ‖(W.multiplier z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
        ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∧
      ‖(W.multiplier z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
        2 * (∫ x, ∑ i, (η x * (z : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) +
          2 * L * ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 := by
  let y := W.multiplier z
  have hzy := Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (y : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
  have hzz := Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (z : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
  have hzval : MemLp ((z : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((z : GradientSpace (N := N) ⊤ q).fst)
  have hyval : MemLp ((y : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((y : GradientSpace (N := N) ⊤ q).fst)
  have hzgrad (i : Fin q) : MemLp ((z : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((z : GradientSpace (N := N) ⊤ q).snd i)
  have hygrad (i : Fin q) : MemLp ((y : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((y : GradientSpace (N := N) ⊤ q).snd i)
  have hD : Integrable (fun x => ∑ i,
      (η x * (z : GradientSpace (N := N) ⊤ q).snd i x) ^ 2) volume :=
    integrable_finsetSum _ (fun i _ =>
      (memLp_two_mul_of_ae_bound hη (hzgrad i) hηb).integrable_sq)
  constructor
  · rw [hzy.1, hzz.1]
    apply integral_mono_ae hyval.integrable_sq hzval.integrable_sq
    filter_upwards [W.value_ae z, hW, hηb] with x hx hw hb
    dsimp only [y]
    rw [hx, hw, mul_pow]
    have habs : -1 ≤ η x ∧ η x ≤ 1 := abs_le.mp (by simpa only [Real.norm_eq_abs] using hb)
    have hsq : η x ^ 2 ≤ 1 := by nlinarith [habs.1, habs.2]
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans_eq (one_mul _)
  · rw [hzy.2, hzz.1]
    have hiY : Integrable (fun x => ∑ i,
        (y : GradientSpace (N := N) ⊤ q).snd i x ^ 2) volume :=
      integrable_finsetSum _ (fun i _ => (hygrad i).integrable_sq)
    have hb := integral_mono_ae hiY
      ((hD.const_mul 2).add (hzval.integrable_sq.const_mul (2 * L))) (by
        filter_upwards [ae_all_iff.mpr (W.gradient_ae z), hW, ae_all_iff.mpr hWd, hd]
          with x hx hw hwd hdw
        have hsq : (∑ i, (y : GradientSpace (N := N) ⊤ q).snd i x ^ 2) ≤
            ∑ i, (2 * (η x * (z : GradientSpace (N := N) ⊤ q).snd i x) ^ 2 +
              2 * (d i x * (z : GradientSpace (N := N) ⊤ q).fst x) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp only [y]
          rw [hx i, hw, hwd i]
          nlinarith only [sq_nonneg (η x * (z : GradientSpace (N := N) ⊤ q).snd i x -
            d i x * (z : GradientSpace (N := N) ⊤ q).fst x)]
        have he : (∑ i, (d i x * (z : GradientSpace (N := N) ⊤ q).fst x) ^ 2) =
            (z : GradientSpace (N := N) ⊤ q).fst x ^ 2 * ∑ i, d i x ^ 2 := by
          simp only [mul_pow, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, he] at hsq
        have herr := mul_le_mul_of_nonneg_left hdw
          (sq_nonneg ((z : GradientSpace (N := N) ⊤ q).fst x))
        simp only [Pi.add_apply]
        nlinarith only [hsq, herr])
    have hs := integral_add (hD.const_mul 2) (hzval.integrable_sq.const_mul (2 * L))
    simp only [Pi.add_apply] at hb
    rw [hs, integral_const_mul, integral_const_mul] at hb
    exact hb

end HeatKernel
