-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLaterStep
public import HeatKernel.Moser.NegativePowerTerminalIteration
public import HeatKernel.Moser.MeanValueCutoffRadii

/-! # Reciprocal essential bounds on terminal later cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Iterating the matrix reciprocal norm step gives an essential bound uniform
in the interior terminal time and every positive initial exponent. -/
theorem exists_uniform_matrix_later_terminal_reciprocal_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (u : ℝ × (Fin N → ℝ) → ℝ),
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
      eLpNormEssSup (fun z => (u z + c)⁻¹)
        ((volume.restrict (Icc (-3 / 2 * ρ ^ 2) b)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * ρ) :
            Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal ((L / (R - ρ) ^ (ν + 2)) ^ (1 / p) *
          (eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            ((volume.restrict (Icc (-3 / 2 * R ^ 2) b)).prod (volume.restrict
              (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * R) :
                Set (Fin N → ℝ))))).toReal) := by
  obtain ⟨K, hK, hstep⟩ := exists_uniform_matrix_later_reciprocal_step_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  have hν0 : 0 < ν := lt_of_le_of_lt (by exact le_trans (by norm_num) (le_max_left _ _)) hν
  obtain ⟨L, hL, hiter⟩ := exists_uniform_negative_power_initial_finite_iteration_constant
    (show 1 ≤ 4 * K by linarith) (show (1 : ℝ) ≤ 4 by norm_num) hν0
  refine ⟨L, hL, ?_⟩
  intro u hum hu0 coeff hu ha hbound b hb hb0 ρ R hρ hρR hR c p hc hp
  let f := fun z => (u z + c)⁻¹
  let radii := nestedCutoffRadius ρ R
  let μ := fun r : ℝ => (volume.restrict (Icc (-3 / 2 * r ^ 2) b)).prod
    (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ)
      (5 / 4 * r) : Set (Fin N → ℝ)))
  have hradii (j : ℕ) : radii j ∈ Icc ρ R := by
    refine ⟨(lt_nestedCutoffRadius hρR j).le, ?_⟩
    induction j with
    | zero => simp only [radii, nestedCutoffRadius_zero, le_refl]
    | succ j hj => exact (nestedCutoffRadius_succ_lt hρR j).le.trans hj
  have hμmono {r₁ r₂ : ℝ} (h0 : 0 ≤ r₁) (h : r₁ ≤ r₂) : μ r₁ ≤ μ r₂ := by
    apply Measure.prod_mono
    · apply Measure.restrict_mono _ le_rfl
      apply Icc_subset_Icc _ le_rfl
      nlinarith
    · apply Measure.restrict_mono _ le_rfl
      intro x hx
      exact Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan)
        (show 5 / 4 * r₁ ≤ 5 / 4 * r₂ by linarith) hx
  have hfiniteV : volume (CarnotPoint.coordinateBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R) : Set (Fin N → ℝ)) ≠ ⊤ := by
    rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by linarith)).ne
  let : IsFiniteMeasure (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R) : Set (Fin N → ℝ))) :=
    isFiniteMeasure_restrict.mpr hfiniteV
  have hshift : AEStronglyMeasurable (fun z => u z + c) (μ R) :=
    (hum.add measurable_const).aestronglyMeasurable
  have hm : MemLp f (ENNReal.ofReal p) (μ R) :=
    memLp_reciprocal_of_positive_lower_bound hc hshift
      (Filter.Eventually.of_forall fun z => le_add_of_nonneg_left (hu0 z)) _
  have hit := hiter (μ ρ) (fun j => μ (radii j)) f (R - ρ) p
    (sub_pos.mpr hρR) (by linarith) hp
    (fun j => hμmono (by linarith) (hradii j).1)
    (by simpa only [radii, nestedCutoffRadius_zero] using hm.eLpNorm_lt_top)
  have hh := hit (by
    intro j
    have hs := hstep u hum hu0 coeff hu ha hbound b hb hb0
      (radii (j + 1)) (radii j) (hρ.trans (hradii (j + 1)).1)
      (nestedCutoffRadius_succ_lt hρR j) ((hradii j).2.trans hR) c
      (p * (1 + 2 / ν) ^ j) hc (by positivity)
    have hgap : K / (radii j - radii (j + 1)) ^ 2 =
        (4 * K) * 4 ^ j / (R - ρ) ^ 2 := by
      have hpow : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
        rw [show (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ], mul_pow,
          ← pow_mul, Nat.mul_comm j 2, pow_mul]
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
        ring
      dsimp only [radii]
      rw [nestedCutoffRadius_sub_succ, div_pow, hpow]
      field_simp
    rw [hgap] at hs
    simpa only [f, μ, pow_succ, mul_assoc] using hs)
  simpa only [radii, nestedCutoffRadius_zero] using hh

end HeatKernel
