-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLaterTerminal
public import HeatKernel.Moser.TopExhaustionReciprocalNormBound

/-! # Reciprocal essential bounds with open top time -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Uniform terminal reciprocal bounds extend to the open top time by
cofinal exhaustion, with the same constant and literal source norm. -/
theorem exists_uniform_matrix_later_open_reciprocal_constant {N q : ℕ}
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
      ∀ ρ R : ℝ, 9 / 10 ≤ ρ → ρ < R → R ≤ 1 →
      ∀ c p : ℝ, 0 < c → 0 < p →
      eLpNormEssSup (fun z => (u z + c)⁻¹)
        ((volume.restrict (Ioo (-3 / 2 * ρ ^ 2) 0)).prod (volume.restrict
          (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * ρ) :
            Set (Fin N → ℝ)))) ≤
        ENNReal.ofReal ((L / (R - ρ) ^ (ν + 2)) ^ (1 / p)) *
          eLpNorm (fun z => (u z + c)⁻¹) (ENNReal.ofReal p)
            ((volume.restrict (Ioo (-3 / 2 * R ^ 2) 0)).prod (volume.restrict
              (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ) (5 / 4 * R) :
                Set (Fin N → ℝ)))) := by
  obtain ⟨L, hL, hterminal⟩ := exists_uniform_matrix_later_terminal_reciprocal_constant
    G hq hqpos hspan hw hν ell upper hell hupper
  refine ⟨L, hL, ?_⟩
  intro u hum hu0 coeff hu ha hbound ρ R hρ hρR hR c p hc hp
  let f := fun z => (u z + c)⁻¹
  let B := (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ)
    (5 / 4 * R) : Set (Fin N → ℝ))
  let B' := (CarnotPoint.coordinateBall G hq hqpos hspan (0 : Fin N → ℝ)
    (5 / 4 * ρ) : Set (Fin N → ℝ))
  have hfiniteB : volume B ≠ ⊤ := by
    dsimp only [B]
    rw [CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan
      (0 : Fin N → ℝ) (5 / 4 * R)]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw 0 (by linarith)).ne
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hfiniteB
  have hshift : AEStronglyMeasurable (fun z => u z + c)
      ((volume.restrict (Icc (-3 / 2 * R ^ 2) 0)).prod (volume.restrict B)) :=
    (hum.add measurable_const).aestronglyMeasurable
  have hm := memLp_reciprocal_of_positive_lower_bound hc hshift
    (Filter.Eventually.of_forall fun z => le_add_of_nonneg_left (hu0 z)) (ENNReal.ofReal p)
  have hcost : 0 ≤ (L / (R - ρ) ^ (ν + 2)) ^ (1 / p) := by positivity
  have he := eLpNormEssSup_prod_Ioo_le_of_ae_terminal_real_norm_bounds
    (volume.prod (volume : Measure (Fin N → ℝ)))
    (a := -3 / 2 * R ^ 2) (a' := -3 / 2 * ρ ^ 2)
    (c := -1 / 2) (T := 0) (by norm_num) B B' f (ENNReal.ofReal p) hcost
    (by simpa only [Measure.prod_restrict] using hm.eLpNorm_lt_top) (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with b hb
      have ht := hterminal u hum hu0 coeff hu ha hbound b hb.1.le hb.2
        ρ R hρ hρR hR c p hc hp
      rw [Measure.prod_restrict, Measure.prod_restrict] at ht
      have hsub : (Ioo (-3 / 2 * ρ ^ 2) b ×ˢ B') ⊆
          Icc (-3 / 2 * ρ ^ 2) b ×ˢ B' := Set.prod_mono Ioo_subset_Icc_self Subset.rfl
      exact (eLpNormEssSup_mono_measure _
        ((Measure.restrict_mono hsub le_rfl).absolutelyContinuous)).trans ht)
  have htime : (volume : Measure ℝ).restrict (Ioo (-3 / 2 * R ^ 2) 0) =
      volume.restrict (Icc (-3 / 2 * R ^ 2) 0) := Measure.restrict_congr_set Ioo_ae_eq_Icc
  rw [← Measure.prod_restrict, ← Measure.prod_restrict, ← htime,
    ENNReal.ofReal_mul hcost, ENNReal.ofReal_toReal (by
      simpa only [← htime] using hm.eLpNorm_lt_top.ne)] at he
  exact he

end HeatKernel
