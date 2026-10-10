-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixPowerMoment
public import HeatKernel.Moser.MeanValueNestedPowerCutoffs
public import HeatKernel.Moser.MeanValueNestedPowerNorms
public import HeatKernel.Moser.MeanValueTimeCutoffs
public import HeatKernel.Moser.MeanValueUnitPowerStepBounds
import Mathlib.Tactic

/-! # Positive-part norm steps for signed matrix weak solutions -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The positive parts of signed uniformly elliptic matrix weak solutions on the unit cylinder satisfy
each nested positive-power norm step with uniform Sobolev and cutoff constants.
All energy and cutoff witnesses are constructed from the equation and geometry.
The constants are uniform over the strictly interior terminal time. -/
theorem exists_uniform_signed_matrix_unit_positive_part_step_constants {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ A K : ℝ, 1 ≤ A ∧ 1 ≤ K ∧ ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
        (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1) u →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ b : ℝ, -1 / 16 ≤ b → b < 0 →
      ∀ r R : ℝ, r ∈ Icc (1 / 2 : ℝ) (7 / 8) →
      R ∈ Icc (1 / 2 : ℝ) (7 / 8) → r < R → ∀ p : ℝ, 2 ≤ p →
      eLpNorm (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0)
        (ENNReal.ofReal (p * (1 + 2 / ν)))
        ((volume.restrict (Icc (-r) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal A ^ (1 / (p * (1 + 2 / ν))) *
          ENNReal.ofReal (K * p ^ 2 / (R - r) ^ 2) ^ (1 / p) *
            eLpNorm (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0) (ENNReal.ofReal p)
              ((volume.restrict (Icc (-R) b)).prod (volume.restrict
                (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) R : Set (Fin N → ℝ)))) := by
  obtain ⟨A, hA, hMoment⟩ := exists_uniform_signed_matrix_positive_power_moment_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  obtain ⟨C, hC, htderiv⟩ := exists_uniform_lowerTimeCutoff_derivative_bound
  have hK : 1 ≤ 100 * (C + 1) * max 1 upper * (max 1 (1 / ell)) ^ 2 := by
    have hbase : 1 ≤ 100 * (C + 1) := by linarith
    have hd : 1 ≤ max 1 upper := le_max_left _ _
    have hc : 1 ≤ (max 1 (1 / ell)) ^ 2 := one_le_pow₀ (le_max_left _ _)
    have hprod : 1 ≤ 100 * (C + 1) * max 1 upper := by nlinarith
    nlinarith
  refine ⟨A, 100 * (C + 1) * max 1 upper * (max 1 (1 / ell)) ^ 2, hA, hK, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop r R hr hR hrR p hp
  let I : Opens ℝ := ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
  let U := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1
  let V := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) R
  let θ := lowerTimeCutoff (-R) (-r)
  obtain ⟨φ, η, hφ, hcφ, hsφ, hφunit, hη, hcη, hsη, hηunit, hηone, hplateau, hdη⟩ :=
    exists_nested_smooth_power_cutoffs G hq hqpos hspan hw (0 : Fin N → ℝ) hrR
  have hJI : Icc (-15 / 16 : ℝ) (b / 2) ⊆ (I : Set ℝ) := by
    intro t ht
    change -1 < t ∧ t < 0
    constructor <;> linarith [ht.1, ht.2]
  have hfinite : volume (V : Set (Fin N → ℝ)) ≠ ⊤ := by
    rw [CarnotPoint.coordinateBall_eq_horizontalBall]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by linarith [hR.1])).ne
  have hsφU : tsupport φ ⊆ (U : Set (Fin N → ℝ)) :=
    hsφ.trans (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan)
      (show R ≤ 1 by linarith [hR.2]))
  have htime : -R < -r := neg_lt_neg hrR
  have hb (M : ℝ) (hM : 0 < M) := hMoment I U V hfinite u coeff hu ha hbound (-15 / 16) (b / 2) (-R) b
    hJI (by linarith [hR.1]) (by linarith [hR.2]) (by linarith)
    φ η hφ hφunit hcφ hsφU hsφ hη hηunit hcη hsη hplateau
    (16 / (R - r) ^ 2) (by positivity) hdη θ
    ((contDiff_lowerTimeCutoff _ _).of_le (by simp))
    (lowerTimeCutoff_eq_zero htime le_rfl) (fun t _ => lowerTimeCutoff_mem_Icc _ _ t)
    (C / (R - r)) (by positivity) (fun t _ => by
      have ht := htderiv (-R) (-r) htime t
      rw [Real.norm_eq_abs] at ht
      exact (le_abs_self (deriv θ t)).trans (by simpa only [neg_sub_neg] using ht)) p hp M hM
  have hvalue (t : ℝ) (x : Fin N → ℝ) :
      max (u t x * φ x) 0 = max (u t x) 0 * φ x := by
    rw [max_mul_of_nonneg _ _ (hφunit x).1, zero_mul]
  have htransform (M : ℝ) (hM : 0 < M) (t : ℝ) (x : Fin N → ℝ) :
      linearTailPositivePower M (p / 2) (max (u t x) 0) =
        linearTailPositivePower M (p / 2) (u t x) :=
    (linearTailPowerWeakSolutionTest_positive_part hM
      (show 1 ≤ p / 2 by linarith only [hp])).1
  have hbpos (M : ℝ) (hM : 0 < M) := hb M hM
  simp_rw [hvalue] at hbpos
  have hcoef := matrix_cutoff_energy_coefficient_le_power_gap_factor (ell := ell) (upper := upper) hC.le (sub_pos.mpr hrR)
    (show R - r ≤ 1 by linarith [hR.2, hr.1]) hp
  have hb' (M : ℝ) (hM : 0 < M) := (hbpos M hM).trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
      (show 0 ≤ 1 + 2 / ν by have hν0 := lt_of_le_of_lt (le_max_left _ _) hν; positivity)))
  have hsub (ρ : ℝ) (hρ : ρ ∈ Icc (1 / 2 : ℝ) (7 / 8)) :
      Icc (-ρ) b ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    constructor <;> linarith [hρ.1, hρ.2, ht.1, ht.2]
  refine eLpNorm_step_le_of_uniform_linearTail_power_moments (neg_le_neg hrR.le)
    hp (lt_of_le_of_lt (le_max_left _ _) hν)
    V.isOpen.measurableSet (fun t x => max (u t x) 0) θ η φ hφunit hsφ ?_ ?_
    ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hu.aestronglyMeasurable_unit_inner_product_cylinder G hq hqpos hspan hw
        (hsub r hr) (by linarith [hr.2]))) ?_ ?_
  · exact Filter.Eventually.of_forall fun _ =>
      Filter.Eventually.of_forall fun x _ => le_max_right _ _
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    filter_upwards [self_mem_ae_restrict
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r).isOpen.measurableSet] with x hx
    change lowerTimeCutoff (-R) (-r) t * η x = 1
    rw [lowerTimeCutoff_eq_one htime ht.1, hηone x (Metric.ball_subset_closedBall hx), one_mul]
  · exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hu.aestronglyMeasurable_unit_inner_product_cylinder G hq hqpos hspan hw
        (hsub R hR) (by linarith [hR.2]))
  · intro M hM
    simpa only [htransform M hM] using hb' M hM

end HeatKernel
