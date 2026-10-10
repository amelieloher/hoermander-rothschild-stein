-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixUnitPowerStep
public import HeatKernel.Moser.MeanValueFiniteIteration
public import HeatKernel.Moser.MeanValueEnergyFactors
public import HeatKernel.Moser.MeanValueCutoffRadii
public import HeatKernel.Moser.MeanValueGapExponent
public import HeatKernel.Moser.MeanValueSignedParts
public import HeatKernel.Moser.WeakSolutionScaling
import Mathlib.Tactic

/-! # Elliptic matrix quadratic mean values with nested-cylinder gaps -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Positive parts of signed uniformly elliptic matrix weak solutions satisfy a quadratic mean-value estimate
on every nested interior unit cylinder, with the exact inverse gap power. The
constant is uniform in the two radii and the strictly interior terminal time. -/
theorem exists_uniform_signed_matrix_unit_positive_part_gap_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
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
      ∀ ρ R : ℝ, ρ ∈ Icc (1 / 2 : ℝ) (7 / 8) →
      R ∈ Icc (1 / 2 : ℝ) (7 / 8) → ρ < R →
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0)
        ((volume.restrict (Icc (-ρ) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) ρ : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal (C * (R - ρ) ^ (-(1 + ν / 2))) *
          eLpNorm (fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0) 2
            ((volume.restrict (Icc (-R) b)).prod (volume.restrict
              (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) R : Set (Fin N → ℝ)))) := by
  obtain ⟨A, K, hA, hK, hstep⟩ :=
    exists_uniform_signed_matrix_unit_positive_part_step_constants G hq hqpos hspan hw hν ell upper hell hupper
  let χ := 1 + 2 / ν
  have hν2 : 2 < ν := lt_of_le_of_lt (le_max_left _ _) hν
  have hχ : 1 < χ := by
    dsimp only [χ]
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) (show 0 < ν by linarith)]
  let C₀ := 16 * A * K
  let B₀ := 4 * χ ^ 2
  have hC₀ : 1 ≤ C₀ := by
    dsimp only [C₀]
    nlinarith [mul_le_mul hA hK (by norm_num) (by linarith : 0 ≤ A)]
  have hB₀ : 1 ≤ B₀ := by dsimp only [B₀]; nlinarith
  let C := C₀ ^ ((1 - χ⁻¹)⁻¹ / 2) * B₀ ^ ((χ⁻¹ / (1 - χ⁻¹) ^ 2) / 2)
  have hC : 0 < C := mul_pos
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hC₀) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hB₀) _)
  refine ⟨C, hC, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop ρ R hρ hR hρR
  let f := fun z : ℝ × (Fin N → ℝ) => max (u z.1 z.2) 0
  let radii := nestedCutoffRadius ρ R
  let μ := fun r : ℝ => (volume.restrict (Icc (-r) b)).prod
    (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) r : Set (Fin N → ℝ)))
  have hradii (j : ℕ) : radii j ∈ Icc ρ R := by
    refine ⟨(lt_nestedCutoffRadius hρR j).le, ?_⟩
    induction j with
    | zero => simp only [radii, nestedCutoffRadius_zero, le_refl]
    | succ j hj => exact (nestedCutoffRadius_succ_lt hρR j).le.trans hj
  have hrange (j : ℕ) : radii j ∈ Icc (1 / 2 : ℝ) (7 / 8) :=
    ⟨hρ.1.trans (hradii j).1, (hradii j).2.trans hR.2⟩
  have hμmono {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : μ r₁ ≤ μ r₂ := by
    apply Measure.prod_mono
    · exact Measure.restrict_mono (Icc_subset_Icc (neg_le_neg h) le_rfl) le_rfl
    · exact Measure.restrict_mono
        (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) h) le_rfl
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδone : R - ρ ≤ 1 := by linarith [hR.2, hρ.1]
  have hgapPos : 0 < C * (R - ρ) ^ (-(1 + ν / 2)) :=
    mul_pos hC (Real.rpow_pos_of_pos hδ _)
  by_cases htop : eLpNorm f 2 (μ R) = ⊤
  · change eLpNormEssSup f (μ ρ) ≤
      ENNReal.ofReal (C * (R - ρ) ^ (-(1 + ν / 2))) * eLpNorm f 2 (μ R)
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hgapPos).ne']
    exact le_top
  have hfinite : eLpNorm f 2 (μ (radii 0)) < ⊤ := by
    simpa only [radii, nestedCutoffRadius_zero] using lt_top_iff_ne_top.mpr htop
  have hit := eLpNormEssSup_le_of_initial_finite_nested_iteration
    (μ ρ) (fun j => μ (radii j)) hC₀ hB₀ hδ hδone hχ
    (fun j => hμmono (hradii j).1) hfinite
  have hnormstep : ∀ j,
      eLpNorm f (ENNReal.ofReal (2 * χ ^ (j + 1))) (μ (radii (j + 1))) ≤
        ENNReal.ofReal ((C₀ * B₀ ^ j / (R - ρ) ^ 2) ^ (1 / (2 * χ ^ j))) *
          eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μ (radii j)) := by
    intro j
    have hp : 2 ≤ 2 * χ ^ j := by nlinarith [one_le_pow₀ (n := j) hχ.le]
    have hs := hstep u coeff hu ha hbound b hbLow hbTop
      (radii (j + 1)) (radii j) (hrange (j + 1)) (hrange j)
      (nestedCutoffRadius_succ_lt hρR j) (2 * χ ^ j) hp
    change eLpNorm f (ENNReal.ofReal ((2 * χ ^ j) * χ)) (μ (radii (j + 1))) ≤
      ENNReal.ofReal A ^ (1 / ((2 * χ ^ j) * χ)) *
        ENNReal.ofReal (K * (2 * χ ^ j) ^ 2 / (radii j - radii (j + 1)) ^ 2) ^
          (1 / (2 * χ ^ j)) * eLpNorm f (ENNReal.ofReal (2 * χ ^ j)) (μ (radii j)) at hs
    have hgap : K * (2 * χ ^ j) ^ 2 / (radii j - radii (j + 1)) ^ 2 =
        2 * ((2 * K) * (2 * χ ^ j) ^ 2 * 4 ^ j / (R - ρ) ^ 2) := by
      have hpow : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
        rw [show (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ], mul_pow,
          ← pow_mul, Nat.mul_comm j 2, pow_mul]
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
        ring
      dsimp only [radii]
      rw [nestedCutoffRadius_sub_succ, div_pow, hpow]
      field_simp
      ring
    have hfac := ennreal_parabolic_energy_iteration_factor_le hA
      (show 0 ≤ 2 * K by linarith) hχ hδ j
    have hD : ENNReal.ofReal (K * (2 * χ ^ j) ^ 2 / (radii j - radii (j + 1)) ^ 2) =
        2 * ENNReal.ofReal ((2 * K) * (2 * χ ^ j) ^ 2 * 4 ^ j / (R - ρ) ^ 2) := by
      rw [hgap, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    have hpexp : (2 * χ ^ j) * χ = 2 * χ ^ (j + 1) := by rw [pow_succ]; ring
    rw [hD, hpexp] at hs
    rw [hpexp] at hfac
    have hh := hs.trans (mul_le_mul' hfac le_rfl)
    simpa only [C₀, B₀, show 8 * A * (2 * K) = 16 * A * K by ring] using hh
  have hb := hit hnormstep
  have hconst : Real.exp (((Real.log C₀ - 2 * Real.log (R - ρ)) / 2) * (1 - χ⁻¹)⁻¹ +
      (Real.log B₀ / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) =
      C * (R - ρ) ^ (-(1 + ν / 2)) := by
    rw [cutoff_iteration_constant_eq_gap_power (zero_lt_one.trans_le hC₀)
      (zero_lt_one.trans_le hB₀) hδ]
    change C * (R - ρ) ^ (-(1 - χ⁻¹)⁻¹) = _
    rw [show (1 - χ⁻¹)⁻¹ = 1 + ν / 2 from parabolic_cutoff_gap_exponent hν2]
  rw [hconst] at hb
  have hreal : ENNReal.ofReal
      ((C * (R - ρ) ^ (-(1 + ν / 2))) * (eLpNorm f 2 (μ (radii 0))).toReal) =
      ENNReal.ofReal (C * (R - ρ) ^ (-(1 + ν / 2))) * eLpNorm f 2 (μ (radii 0)) := by
    rw [ENNReal.ofReal_mul hgapPos.le, ENNReal.ofReal_toReal hfinite.ne]
  simpa only [radii, nestedCutoffRadius_zero] using hb.trans_eq hreal

/-- Signed matrix weak solutions satisfy the quadratic estimate with the same gap power. -/
theorem exists_uniform_signed_matrix_unit_gap_essential_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
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
      ∀ ρ R : ℝ, ρ ∈ Icc (1 / 2 : ℝ) (7 / 8) →
      R ∈ Icc (1 / 2 : ℝ) (7 / 8) → ρ < R →
      eLpNormEssSup (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
        ((volume.restrict (Icc (-ρ) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) ρ : Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal (C * (R - ρ) ^ (-(1 + ν / 2))) *
          eLpNorm (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
            ((volume.restrict (Icc (-R) b)).prod (volume.restrict
              (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) R : Set (Fin N → ℝ)))) := by
  obtain ⟨C, hC, hgap⟩ := exists_uniform_signed_matrix_unit_positive_part_gap_bound
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro u coeff hu ha hbound b hbLow hbTop ρ R hρ hR hρR
  have htime : Icc (-R) b ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    constructor <;> linarith only [hR.2, hbTop, ht.1, ht.2]
  have hm := hu.aestronglyMeasurable_unit_inner_product_cylinder G hq hqpos hspan hw
    htime (show R ≤ 1 by linarith only [hR.2])
  have hnweak : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo (-1 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) 1)
      (fun t x => -u t x) := by
    simpa only [neg_one_mul] using
      IsLocalWeakSolution.const_mul G hq hqpos hw hspan hu (-1)
  exact eLpNormEssSup_le_mul_eLpNorm_of_positive_negative_parts hm
    (hgap u coeff hu ha hbound b hbLow hbTop ρ R hρ hR hρR)
    (hgap (fun t x => -u t x) coeff hnweak ha hbound b hbLow hbTop ρ R hρ hR hρR)

end HeatKernel
