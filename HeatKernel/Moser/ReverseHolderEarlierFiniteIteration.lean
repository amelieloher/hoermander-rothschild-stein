-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderEarlierStep
public import HeatKernel.Moser.ReverseHolderInitialFiniteIteration
public import HeatKernel.Moser.ReverseHolderReferenceNorms
public import HeatKernel.Moser.MeanValueCutoffRadii
import Mathlib.Tactic

/-! Finite normalized reverse-Hölder bounds on earlier unit cylinders. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A finite reference mass covering the full unit earlier cylinder gives the
normalized reverse-Hölder estimate. The reference-mass geometry is explicit;
the weak equation supplies every small-power step and its finite starting norm. -/
theorem exists_uniform_matrix_earlier_finite_constant_of_reference_mass {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper)
    (m : ℝ≥0∞) (hm : m ≠ 0) (hmtop : m ≠ ⊤)
    (hmref : ((volume.restrict (Icc (-25 / 8 : ℝ) (-15 / 8))).prod
      (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
        (0 : Fin N → ℝ) (5 / 4) : Set (Fin N → ℝ)))) univ ≤ m) :
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
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p → p ≤ 1 / 4 →
      eLpNorm (fun z => u z + c) (ENNReal.ofReal (1 / 2))
        (m⁻¹ • ((volume.restrict (Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * ρ ^ 2))).prod
          (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
            (0 : Fin N → ℝ) (5 / 4 * ρ) : Set (Fin N → ℝ))))) ≤
        ENNReal.ofReal ((L / (R - ρ) ^ (2 * (ν + 2))) ^ (1 / p - 1 / (1 / 2))) *
          eLpNorm (fun z => u z + c) (ENNReal.ofReal p)
            (m⁻¹ • ((volume.restrict (Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * R ^ 2))).prod
              (volume.restrict (CarnotPoint.coordinateBall G hq hqpos hspan
                (0 : Fin N → ℝ) (5 / 4 * R) : Set (Fin N → ℝ))))) := by
  obtain ⟨K, hK, hstep⟩ := exists_uniform_matrix_earlier_small_power_step_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  let D := K * max 1 m.toReal * max 1 m.toReal⁻¹
  have hD : 1 ≤ D := by
    have h1 := le_max_left (1 : ℝ) m.toReal
    have h2 := le_max_left (1 : ℝ) m.toReal⁻¹
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK h1) h2
  have hν0 : 0 < ν := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left _ _)) hν
  obtain ⟨L, hL, hiter⟩ := exists_uniform_reverse_holder_initial_finite_iteration_constant
    (show 1 ≤ 4 * D by linarith) (show (1 : ℝ) ≤ 4 by norm_num) hν0
  refine ⟨L, hL, ?_⟩
  intro u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp hp4
  let f := fun z => u z + c
  let radii := nestedCutoffRadius ρ R
  let μ := fun r : ℝ => (volume.restrict (Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * r ^ 2))).prod
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
      apply Icc_subset_Icc le_rfl
      nlinarith
    · exact Measure.restrict_mono
        (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) (by linarith)) le_rfl
  have hmass : (m⁻¹ • μ ρ) univ ≤ 1 := by
    rw [Measure.smul_apply, smul_eq_mul]
    have hμone : (μ 1) univ ≤ m := by
      simpa only [μ, one_pow, mul_one, show (-25 / 8 + 5 / 4 : ℝ) = -15 / 8 by norm_num]
        using hmref
    exact (mul_le_mul' le_rfl ((hμmono (by linarith) (by linarith : ρ ≤ 1)) univ |>.trans hμone)).trans_eq
      (ENNReal.inv_mul_cancel hm hmtop)
  let x₀ : CarnotPoint G hq hqpos hspan := (0 : Fin N → ℝ)
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) :=
    CarnotPoint.properSpace G hq hqpos hspan hw
  have hJI : Icc (-25 / 8 : ℝ) (-25 / 8 + 5 / 4 * R ^ 2) ⊆ Ioo (-4 : ℝ) 0 := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2, sq_nonneg (R - 1)]
  have hu2 : MemLp u 2 (μ R) := by
    dsimp only [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan coeff
      ⟨Ioo (-4 : ℝ) 0, isOpen_Ioo⟩
      (CarnotPoint.coordinateBall G hq hqpos hspan x₀ 2)
      isCompact_Icc hJI (isCompact_closedBall x₀ (3 / 2))
      (Metric.closedBall_subset_ball (α := CarnotPoint G hq hqpos hspan) (by norm_num))).mono_measure
        (Measure.restrict_mono (prod_mono Subset.rfl
          ((Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan)
            (show 5 / 4 * R ≤ 3 / 2 by linarith)).trans Metric.ball_subset_closedBall)) le_rfl)
  have hμfinite : (μ R) univ ≠ ⊤ :=
    ne_top_of_le_ne_top hmtop (((hμmono (by linarith) hR) univ).trans (by
      simpa only [μ, one_pow, mul_one, show (-25 / 8 + 5 / 4 : ℝ) = -15 / 8 by norm_num]
        using hmref))
  let : IsFiniteMeasure (μ R) := ⟨hμfinite.lt_top⟩
  have hf : MemLp f (ENNReal.ofReal p) (μ R) :=
    (hu2.add (memLp_const c)).mono_exponent (by
      exact (ENNReal.ofReal_le_ofReal (show p ≤ 2 by linarith)).trans_eq (by norm_num))
  have hfn : eLpNorm f (ENNReal.ofReal p) (m⁻¹ • μ R) < ⊤ :=
    (hf.smul_measure (ENNReal.inv_ne_top.mpr hm)).eLpNorm_lt_top
  have hit := hiter (m⁻¹ • μ ρ) (fun j => m⁻¹ • μ (radii j)) f (R - ρ) p (1 / 2)
    hmass (sub_pos.mpr hρR) (by linarith) hp (by norm_num) (by linarith)
    (fun j S => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl (hμmono (by linarith) (hradii j).1 S))
    (by simpa only [radii, nestedCutoffRadius_zero] using hfn)
  have hh := hit (by
    intro j hj
    have hpj : 0 < p * (1 + 2 / ν) ^ j := by positivity
    have hs := hstep u hum hu0 coeff hu ha hbound
      (radii (j + 1)) (radii j) (hρ.trans (hradii (j + 1)).1)
      (nestedCutoffRadius_succ_lt hρR j) ((hradii j).2.trans hR) c
      (p * (1 + 2 / ν) ^ j) hc hpj hj
    have hsn := eLpNorm_small_power_step_le_after_reference_normalization
      (μ (radii (j + 1))) (μ (radii j)) f hm hmtop hpj
      (show 1 ≤ 1 + 2 / ν from le_add_of_nonneg_right (by positivity))
      (show 0 ≤ K / (radii j - radii (j + 1)) ^ 2 by positivity) hs
    have hgap : K / (radii j - radii (j + 1)) ^ 2 * max 1 m.toReal * max 1 m.toReal⁻¹ =
        (4 * D) * 4 ^ j / (R - ρ) ^ 2 := by
      have hpow : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
        rw [show (2 : ℝ) ^ (j + 1) = 2 ^ j * 2 by rw [pow_succ], mul_pow,
          ← pow_mul, Nat.mul_comm j 2, pow_mul]
        rw [show (2 : ℝ) ^ 2 = 4 by norm_num]
        ring
      dsimp only [radii, D]
      rw [nestedCutoffRadius_sub_succ, div_pow, hpow]
      field_simp
    rw [hgap] at hsn
    simpa only [f, μ, pow_succ, mul_assoc] using hsn)
  simpa only [radii, nestedCutoffRadius_zero] using hh

end HeatKernel
