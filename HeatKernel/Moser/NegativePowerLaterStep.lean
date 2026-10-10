-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerMatrixPowerMoment
public import HeatKernel.Moser.NegativePowerOuterMomentStep
public import HeatKernel.Moser.MeanValueNestedPowerCutoffs
public import HeatKernel.Moser.MeanValueTimeCutoffs

/-! # Uniform reciprocal norm steps on later Harnack cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Reciprocal cutoff energy costs have an inverse squared gap bound,
independently of the positive reciprocal exponent. -/
theorem reciprocal_cutoff_energy_coefficient_le_gap_factor
    {C δ ell upper : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hell : 0 < ell) (_hupper : 0 ≤ upper) :
    (2 * (C / δ) + 2 * upper * (16 / δ ^ 2)) +
      (2 * (C / δ) + 2 * upper * (16 / δ ^ 2)) / ell +
        2 * (16 / δ ^ 2) + 1 ≤
      ((2 * C + 32 * upper) * (1 + 1 / ell) + 33) / δ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  have he : ((2 * (C / δ) + 2 * upper * (16 / δ ^ 2)) +
      (2 * (C / δ) + 2 * upper * (16 / δ ^ 2)) / ell +
        2 * (16 / δ ^ 2) + 1) * δ ^ 2 =
      (2 * C * δ + 32 * upper) * (1 + 1 / ell) + 32 + δ ^ 2 := by
    field_simp
    ring
  rw [he]
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hδone (show 0 ≤ 2 * C by positivity)
  have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 1 + 1 / ell by positivity)
  nlinarith only [hδsq, h2]

/-- The matrix weak equation supplies every reciprocal norm step on the
normalized later cylinders. The constant is independent of the terminal time,
initial exponent, and positive perturbation. -/
theorem exists_uniform_matrix_later_reciprocal_step_constant {N q : ℕ}
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
      ∀ b : ℝ, -1 / 2 ≤ b → b < 0 →
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p →
      eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal (p * (1 + 2 / ν)))
        ((volume.restrict (Icc (-3 / 2 * ρ ^ 2) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * ρ) :
            Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal ((K / (R - ρ) ^ 2) ^ (1 / p)) *
          eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            ((volume.restrict (Icc (-3 / 2 * R ^ 2) b)).prod (volume.restrict
              (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * R) :
                Set (Fin N → ℝ)))) := by
  obtain ⟨A, hA, hmoment⟩ := exists_uniform_matrix_reciprocal_power_moment_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  obtain ⟨C, hC, htime⟩ := exists_uniform_lowerTimeCutoff_derivative_bound
  let K := (2 * C + 32 * upper) * (1 + 1 / ell) + 33
  have hν2 : 2 < ν := lt_of_le_of_lt (le_max_left _ _) hν
  have hν0 : 0 < ν := by linarith
  have hKlocal : 33 ≤ K := by
    have hprod : 0 ≤ (2 * C + 32 * upper) * (1 + 1 / ell) := by positivity
    dsimp only [K]
    linarith
  have hK : 1 ≤ 2 * A * K := by nlinarith
  refine ⟨2 * A * K, hK, ?_⟩
  intro u hum hu0 coeff hu ha hbound b hb hb0 ρ R hρ hρR hR c p hc hp
  let I : Opens ℝ := ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
  let U := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 2
  let V := CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * R)
  let a := -3 / 2 * R ^ 2
  let a' := -3 / 2 * ρ ^ 2
  let θ := lowerTimeCutoff a a'
  have hρ0 : 0 < ρ := by linarith
  have hR0 : 0 < R := hρ0.trans hρR
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδone : R - ρ ≤ 1 := by linarith
  have hspace : 5 / 4 * ρ < 5 / 4 * R := by linarith
  have hgap : R - ρ ≤ a' - a := by dsimp only [a, a']; nlinarith
  have haa' : a < a' := by linarith
  have hJI : Icc (-3 : ℝ) (b / 2) ⊆ (I : Set ℝ) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hfinite : volume (V : Set (Fin N → ℝ)) ≠ ⊤ := by
    dsimp only [V]
    rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by positivity)).ne
  obtain ⟨φ, η, hφ, hcφ, hsφ, hφunit, hη, hcη, hsη, hηunit, hηone, hplateau, hdη⟩ :=
    exists_nested_smooth_power_cutoffs G hq hqpos hspan hw (0 : Fin N → ℝ) hspace
  have hd (x : Fin N → ℝ) : (∑ i, fieldDerivative (G.horizontalFields hq i) η x ^ 2) ≤
      16 / (R - ρ) ^ 2 := by
    apply (hdη x).trans
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith only [sq_nonneg (R - ρ), hδ]
  have hθd (s : ℝ) : deriv θ s ≤ C / (R - ρ) := by
    have ht := htime a a' haa' s
    rw [Real.norm_eq_abs] at ht
    exact (le_abs_self _).trans (ht.trans
      (div_le_div_of_nonneg_left hC.le hδ hgap))
  have hm := hmoment I U V hfinite u hum hu0 coeff hu ha hbound
    (-3) (b / 2) a b hJI (by dsimp only [a]; nlinarith)
    (by dsimp only [a]; nlinarith [sq_nonneg R]) (by linarith)
    φ η hφ hφunit hcφ (hsφ.trans (Metric.ball_subset_ball
      (α := CarnotPoint G hq hqpos hspan) (show 5 / 4 * R ≤ 2 by linarith)))
    hsφ hη hηunit hcη hsη hplateau (16 / (R - ρ) ^ 2) (by positivity) hd θ
    ((contDiff_lowerTimeCutoff _ _).of_le (by simp))
    (lowerTimeCutoff_eq_zero haa' le_rfl) (fun s _ => lowerTimeCutoff_mem_Icc _ _ s)
    (C / (R - ρ)) (by positivity) (fun s _ => hθd s) c p hc hp
  have hcoef := reciprocal_cutoff_energy_coefficient_le_gap_factor hC.le hδ hδone hell hupper
  have hm' := hm.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
      (show 0 ≤ 1 + 2 / ν by positivity)))
  have hs := eLpNorm_reciprocal_step_le_of_outer_moment haa'.le hc hp
    hν2 hA (show 0 ≤ K / (R - ρ) ^ 2 by
      dsimp only [K]; positivity) hfinite u hum hu0 θ η (by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
        filter_upwards [self_mem_ae_restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * ρ)).isOpen.measurableSet]
          with x hx
        dsimp only [θ]
        rw [lowerTimeCutoff_eq_one haa' hs.1, hηone x (Metric.ball_subset_closedBall hx), one_mul]) hm'
  convert hs using 1
  congr 3
  ring

end HeatKernel
