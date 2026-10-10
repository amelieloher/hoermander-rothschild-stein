-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerSobolevEnergy
public import HeatKernel.Moser.NegativePowerMoment

/-! # Complete reciprocal half-power graph energies -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The affine reciprocal half-power graph has exactly the weighted reciprocal
value moment. Its complete gradient is bounded by the principal diffusion and
the cutoff-gradient moment, independently of the positive exponent. -/
theorem WeakSolutionSpatialWeight.negative_half_power_graph_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    {c p K : ℝ} (hc : 0 < c) (hp : 0 < p)
    (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hW : ∀ x, W.toFun x = η x) (hWd : ∀ i x, W.gradient i x = d i x)
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hd : ∀ i, MemLp (d i) 2 volume) :
    let Y := W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc
      (p := -p / 2) (by linarith)) w (c ^ (-p / 2)) z
    ‖(Y : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
      (∫ x, η x ^ 2 * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) ∧
      ‖(Y : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
        2 * (p / 2) ^ 2 * (∫ x, coordinateNormSq
          (fun i => η x * (((z : GradientSpace (N := N) ⊤ q).fst x + c) ^
            (-p / 2 - 1) * (z : GradientSpace (N := N) ⊤ q).snd i x))) +
        2 * (∫ x, ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
          coordinateNormSq (fun i => d i x)) := by
  dsimp only
  let Y := W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc
    (p := -p / 2) (by linarith)) w (c ^ (-p / 2)) z
  let s := fun x => (z : GradientSpace (N := N) ⊤ q).fst x + c
  have hval : (Y : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η x * s x ^ (-p / 2) := by
    filter_upwards [W.affineEnergyMap_value_ae hX
      (shiftedRpowWeakSolutionTest hc (p := -p / 2) (by linarith))
      w (c ^ (-p / 2)) hw z, hz] with x hx hn
    rw [hx, hW, show (shiftedRpowWeakSolutionTest hc
      (p := -p / 2) (by linarith)).toFun ((z : GradientSpace (N := N) ⊤ q).fst x) =
        s x ^ (-p / 2) - c ^ (-p / 2) from
          Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := -p / 2) hn,
      sub_add_cancel]
  have hgrad (i : Fin q) : (Y : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => η x * (((-p / 2) * s x ^ (-p / 2 - 1)) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) + d i x * s x ^ (-p / 2) := by
    simpa only [hW, hWd] using W.shifted_rpow_affine_gradient_ae hX hc
      (by linarith : -p / 2 ≤ 1) z w hz hdw i
  have hn := Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (Y : GradientSpace (N := N) ⊤ q) hval hgrad
  have hv : MemLp ((z : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst
  have hg (i : Fin q) : MemLp ((z : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((z : GradientSpace (N := N) ⊤ q).snd i)
  constructor
  · rw [hn.1]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    rw [mul_pow]
    have he := negative_power_weighted_coordinate_norm_sq (fun _ : Fin 1 => (1 : ℝ))
      (show 0 < s x by dsimp only [s]; linarith) p
    simp only [coordinateNormSq, Fin.sum_univ_one, mul_one, one_pow] at he
    rw [he]
  · rw [hn.2]
    have hb := (integrable_negative_half_power_product_gradient_energy_and_bound hc hp
      hv.aestronglyMeasurable hz hη hηb hg hd).2.2.2
    simpa only [s, coordinateNormSq, integral_const_mul, mul_assoc] using hb

end HeatKernel
