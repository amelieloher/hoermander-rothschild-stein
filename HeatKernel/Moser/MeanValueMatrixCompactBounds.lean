-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixNestedCylinders
public import HeatKernel.Bridge.ParabolicValueIntegrability
import Mathlib.Tactic

/-! # Finite essential bounds on interior cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A signed weak solution has a finite essential supremum on a smaller
cylinder whenever the closed outer cylinder lies inside its domain. -/
theorem IsLocalWeakSolution.eLpNormEssSup_nested_cylinder_lt_top {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {ell upper : ℝ} (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    {a A b ρ R : ℝ} (x₀ : CarnotPoint G hq hqpos hspan)
    (htime : a < A) (hspace : ρ < R) (hI : Icc a b ⊆ (I : Set ℝ))
    (hU : (@Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x₀ R :
      Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ))) :
    eLpNormEssSup (Function.uncurry u) (volume.restrict
      (Ioo A b ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ)) < ⊤ := by
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) :=
    CarnotPoint.properSpace G hq hqpos hspan hw
  let K : Set (Fin N → ℝ) := @Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x₀ R
  have hK : IsCompact K := isCompact_closedBall x₀ R
  have hball : horizontalBall (G.horizontalFields hq) x₀ R ⊆ K := by
    rw [← CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x₀ R]
    exact Metric.ball_subset_closedBall (α := CarnotPoint G hq hqpos hspan)
  have hmem := hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan coeff I U
    isCompact_Icc hI hK hU
  have hmem' : MemLp (Function.uncurry u) 2 (volume.restrict
      (Ioo a b ×ˢ horizontalBall (G.horizontalFields hq) x₀ R)) :=
    hmem.mono_measure (Measure.restrict_mono (Set.prod_mono Ioo_subset_Icc_self hball) le_rfl)
  have hweak : IsLocalWeakSolution G hq hqpos hw hspan coeff
      ⟨Ioo a b, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x₀ R,
        isOpen_horizontalBall G hq hqpos hspan x₀ R⟩ u :=
    hu.mono (Ioo_subset_Icc_self.trans hI) (hball.trans hU)
  obtain ⟨r, hr, hgap, hstart⟩ := exists_positive_radius_for_cylinder_gaps hspace htime
  obtain ⟨C, _, hmean⟩ := exists_uniform_signed_matrix_nested_cylinder_quadratic_bound
    G hq hqpos hspan hw ell upper hell hupper
  have hle := hmean a A b x₀ ρ R r hr hgap hstart (Function.uncurry u) coeff hweak ha hbound
  refine hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / (2 : ℝ)) ENNReal.ofReal_ne_top)
    hmem'.eLpNorm_lt_top

/-- The finite mean-value bound supplies both real essential bounds used in
oscillation estimates for signed solutions. -/
theorem IsLocalWeakSolution.isBoundedUnder_nested_cylinder {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I U u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {ell upper : ℝ} (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    {a A b ρ R : ℝ} (x₀ : CarnotPoint G hq hqpos hspan)
    (htime : a < A) (hspace : ρ < R) (hI : Icc a b ⊆ (I : Set ℝ))
    (hU : (@Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x₀ R :
      Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ))) :
    Filter.IsBoundedUnder (· ≤ ·) (ae (volume.restrict
        (Ioo A b ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ))) (Function.uncurry u) ∧
      Filter.IsBoundedUnder (· ≥ ·) (ae (volume.restrict
        (Ioo A b ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ))) (Function.uncurry u) := by
  have hfinite := hu.eLpNormEssSup_nested_cylinder_lt_top G hq hqpos hspan hw
    ha hell hupper hbound x₀ htime hspace hI hU
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hfinite
  have hnorm : ∀ᵐ z ∂(volume.restrict
      (Ioo A b ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ)),
      ‖u z.1 z.2‖ ≤ (C : ℝ) := by
    filter_upwards [hC] with z hz
    exact_mod_cast hz
  constructor
  · refine ⟨(C : ℝ), ?_⟩
    exact hnorm.mono fun z hz => (le_abs_self (u z.1 z.2)).trans hz
  · refine ⟨-(C : ℝ), ?_⟩
    exact hnorm.mono fun z hz => neg_le_of_abs_le hz

end HeatKernel
