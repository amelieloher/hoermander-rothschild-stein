-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderMatrixCompactMoments
public import HeatKernel.Moser.ReverseHolderOuterMomentStep
public import HeatKernel.Moser.ReverseHolderTimeCutoffs
public import HeatKernel.Moser.NegativePowerLaterStep
public import HeatKernel.Bridge.ParabolicValueIntegrability
import Mathlib.Tactic

/-! Uniform backward small-power norm steps on earlier Harnack cylinders. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The matrix weak equation supplies each small-positive-power norm step on
the normalized earlier cylinders. Its constant is uniform up to the fixed
concave-power endpoint and independent of the positive perturbation. -/
theorem exists_uniform_matrix_earlier_small_power_step_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (u : ℝ × (Fin N → ℝ) → ℝ),
      Measurable u → (∀ z, 0 ≤ u z) →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
        (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 2)
        (fun t x => u (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p → p ≤ 1 / 2 →
      eLpNorm (fun z => u z + c) (ENNReal.ofReal (p * (1 + 2 / ν)))
        ((volume.restrict (Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * ρ ^ 2))).prod
          (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
            (0 : Fin N → ℝ) (5 / 4 * ρ) : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal ((K / (R - ρ) ^ 2) ^ (1 / p)) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p)
            ((volume.restrict (Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * R ^ 2))).prod
              (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
                (0 : Fin N → ℝ) (5 / 4 * R) : Set (Fin N → ℝ)))) := by
  obtain ⟨A, hA, hmoment⟩ := exists_uniform_matrix_reverse_holder_compact_moment_constant
    G hq hqpos hspan hw hν
  obtain ⟨C, hC, htime⟩ := exists_uniform_backward_time_cutoff_bound
  let K := (2 * C + 32 * upper) * (1 + 1 / ell) + 33
  have hν2 : 2 < ν := lt_of_le_of_lt (le_max_left _ _) hν
  have hν0 : 0 < ν := by linarith
  have hKlocal : 33 ≤ K := by
    have hprod : 0 ≤ (2 * C + 32 * upper) * (1 + 1 / ell) := by positivity
    dsimp only [K]
    linarith
  refine ⟨2 * A * K, by nlinarith, ?_⟩
  intro u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp hp2
  let I : Opens ℝ := ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
  let U := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 2
  let V := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * R)
  let a : ℝ := -25 / 8
  let b : ℝ := a + 5 / 4 * R ^ 2
  let b' : ℝ := a + 5 / 4 * ρ ^ 2
  have hρ0 : 0 < ρ := by linarith
  have hR0 : 0 < R := hρ0.trans hρR
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδone : R - ρ ≤ 1 := by linarith
  have hspace : 5 / 4 * ρ < 5 / 4 * R := by linarith
  have hgap : R - ρ ≤ b - b' := by dsimp only [b, b']; nlinarith
  have hb'b : b' < b := by linarith
  have hab : a < b := by dsimp only [b]; nlinarith [sq_pos_of_pos hR0]
  have hJI : Icc (-7 / 2 : ℝ) (-3 / 2) ⊆ (I : Set ℝ) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hbB : b < -3 / 2 := by
    dsimp only [b, a]
    nlinarith [sq_nonneg (R - 1)]
  have hfinite : volume (V : Set (Fin N → ℝ)) ≠ ⊤ := by
    dsimp only [V]
    rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by positivity)).ne
  let : IsFiniteMeasure (volume.restrict (V : Set (Fin N → ℝ))) :=
    isFiniteMeasure_restrict.mpr hfinite
  obtain ⟨φ, η, hφ, hcφ, hsφ, hφunit, hη, hcη, hsη, hηunit, hηone, hplateau, hdη⟩ :=
    exists_nested_smooth_power_cutoffs G hq hqpos hspan hw (0 : Fin N → ℝ) hspace
  have hVU : (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) :=
    Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) (by linarith)
  let x₀ : CarnotPoint G hq hqpos hspan := (0 : Fin N → ℝ)
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) :=
    CarnotPoint.properSpace G hq hqpos hspan hw
  let Kbig : Set (Fin N → ℝ) :=
    @Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x₀ (3 / 2)
  have hKU : Kbig ⊆ (U : Set (Fin N → ℝ)) :=
    Metric.closedBall_subset_ball (α := CarnotPoint G hq hqpos hspan) (by norm_num)
  have hJI' : Icc a b ⊆ (I : Set ℝ) := by
    intro s hs
    constructor <;> dsimp only [a] at * <;> linarith [hs.1, hs.2]
  have hu2 : MemLp u 2 ((volume.restrict (Icc a b)).prod
      (volume.restrict (V : Set (Fin N → ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan coeff I U
      isCompact_Icc hJI' (isCompact_closedBall x₀ (3 / 2)) hKU).mono_measure
        (Measure.restrict_mono (prod_mono Subset.rfl
          ((Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan)
            (show 5 / 4 * R ≤ 3 / 2 by linarith)).trans Metric.ball_subset_closedBall)) le_rfl)
  have hmV := integrable_shifted_small_power_outer_moment
    (volume.restrict (Icc a b)) (volume.restrict (V : Set (Fin N → ℝ)))
      hc hp.le (show p ≤ 1 by linarith) hu2 (Filter.Eventually.of_forall hu0)
  let : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    isFiniteMeasure_restrict.mpr hcφ.isCompact.measure_lt_top.ne
  have hmK := integrable_shifted_small_power_outer_moment
    (volume.restrict (Icc a b)) (volume.restrict (tsupport φ))
      hc hp.le (show p ≤ 1 by linarith)
      (hu2.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hsφ le_rfl)))
      (Filter.Eventually.of_forall hu0)
  have hmKV : (∫ s in Icc a b, ∫ x in tsupport φ, (u (s, x) + c) ^ p) ≤
      ∫ s in Icc a b, ∫ x in (V : Set (Fin N → ℝ)), (u (s, x) + c) ^ p := by
    apply integral_mono_ae hmK.1 hmV.1
    filter_upwards [hmV.2.1] with s hs
    exact setIntegral_mono_set hs (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (add_nonneg (hu0 (s, x)) hc.le) p) (Filter.Eventually.of_forall hsφ)
  have hd (x : Fin N → ℝ) : coordinateNormSq
      (fun i => fieldDerivative (G.horizontalFields hq i) η x) ≤ 16 / (R - ρ) ^ 2 := by
    apply (hdη x).trans
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith only [sq_nonneg (R - ρ), hδ]
  obtain ⟨θ, hθ, hθunit, hθone, hθzero, hθbound⟩ := htime b' b hb'b
  have hθd (s : ℝ) : -deriv (fun t => θ t ^ 2) s ≤ 2 * (C / (R - ρ)) := by
    apply (hθbound s).trans
    convert div_le_div_of_nonneg_left (show 0 ≤ 2 * C by positivity) hδ hgap using 1; ring
  have hm := hmoment ell upper hell hupper I U V hfinite
    (fun t x => u (t, x)) coeff hu (Filter.Eventually.of_forall fun z => hu0 z)
    ha hbound (-7 / 2) (-3 / 2) a b hJI hab (by dsimp only [a]; norm_num) hbB
    (tsupport φ) hcφ.isCompact (hsφ.trans hVU) φ η hφ hφunit hcφ Subset.rfl hsφ
    hη hηunit hcη hsη hplateau (16 / (R - ρ) ^ 2) (by positivity) hd
    θ hθ (hθzero b le_rfl) (fun s _ => hθunit s)
    (2 * (C / (R - ρ))) (by positivity) (fun s _ => hθd s) p c hp hp2 hc
  have hcoef := reciprocal_cutoff_energy_coefficient_le_gap_factor hC.le hδ hδone hell hupper
  have hm' := hm.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' (ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hcoef))
      (ENNReal.ofReal_le_ofReal hmKV)) (show 0 ≤ 1 + 2 / ν by positivity)))
  have hs := eLpNorm_small_power_step_le_of_outer_moment hb'b.le hc hp
    (show p ≤ 1 by linarith) hν2 hA (show 0 ≤ K / (R - ρ) ^ 2 by
      dsimp only [K]; positivity) hfinite u hum hu0 hu2 θ η (by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
        filter_upwards [self_mem_ae_restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * ρ)).isOpen.measurableSet]
          with x hx
        rw [hθone s hs.2, hηone x (Metric.ball_subset_closedBall hx), one_mul]) hm'
  convert hs using 1
  congr 3
  ring

end HeatKernel
