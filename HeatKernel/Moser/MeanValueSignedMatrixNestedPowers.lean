-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueSignedMatrixPositivePowers
public import HeatKernel.Moser.MeanValueWeakRestriction
public import HeatKernel.Moser.MeanValueInteriorCylinders
public import HeatKernel.Moser.MeanValueLocalEssentialBounds
import Mathlib.Tactic

/-! # Positive-power mean values on arbitrary nested elliptic cylinders -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Every positive power gives a mean-value estimate on a nested cylinder with
independent spatial and lower-time gaps. A small radius fitting both gaps pays
the explicit parabolic factor. The constant is independent of every cylinder,
the small radius and the solution. No continuity or preliminary boundedness
is assumed, and the inner cylinder may reach its open top. -/
theorem exists_uniform_signed_matrix_nested_cylinder_positive_power_bound {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {p : ℝ} (hp : 0 < p)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a A T : ℝ) (x₀ : Fin N → ℝ) (ρ R r : ℝ),
      0 < r → r ≤ R - ρ → r ^ 2 ≤ A - a →
      ∀ (v : ℝ × (Fin N → ℝ) → ℝ)
      (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan
        coeff
        ⟨Ioo a T, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x₀ R,
          isOpen_horizontalBall G hq hqpos hspan x₀ R⟩ (fun t x => v (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      eLpNormEssSup v (volume.restrict
        (Ioo A T ×ˢ horizontalBall (G.horizontalFields hq) x₀ ρ)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal ((r ^ (G.homogeneousDimension + 2))⁻¹) ^ (1 / p) *
          eLpNorm v (ENNReal.ofReal p) (volume.restrict
            (Ioo a T ×ˢ horizontalBall (G.horizontalFields hq) x₀ R))) := by
  let ν := max 2 (G.homogeneousDimension : ℝ) + 1
  obtain ⟨C, hC, hmean⟩ := exists_uniform_signed_matrix_cylinder_positive_power_bound
    G hq hqpos hspan hw (ν := ν) (by dsimp only [ν]; linarith) hp ell upper hell hupper
  refine ⟨C, hC, ?_⟩
  intro a A T x₀ ρ R r hr hspace htime v coeff hweak ha hbound
  have hBall (x : Fin N → ℝ) (s : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x s : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) x s :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  apply eLpNormEssSup_restrict_le_of_local_bounds volume
    (isOpen_Ioo.prod (isOpen_horizontalBall G hq hqpos hspan x₀ ρ))
  intro z hz
  let b := interiorCylinderTop T z.1 r
  have hItime : Ioo (b - r ^ 2) b ⊆ Ioo a T :=
    outer_time_interiorCylinderTop_subset hz.1 htime
  have hx : z.2 ∈ (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x₀ ρ : Set (Fin N → ℝ)) := by
    rw [hBall]
    exact hz.2
  have hUspace : horizontalBall (G.horizontalFields hq) z.2 r ⊆
      horizontalBall (G.horizontalFields hq) x₀ R := by
    simpa only [hBall] using
      ball_subset_outer_ball_of_radius_gap (α := CarnotPoint G hq hqpos hspan) hx hspace
  have hsmallweak : IsLocalWeakSolution G hq hqpos hw hspan
      coeff
      ⟨Ioo (b - r ^ 2) b, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) z.2 r,
        isOpen_horizontalBall G hq hqpos hspan z.2 r⟩ (fun t x => v (t, x)) :=
    hweak.mono hItime hUspace
  have hb := hmean b z.2 r hr v coeff hsmallweak ha hbound
  let S := Ioo (b - r ^ 2 / 2) b ×ˢ horizontalBall (G.horizontalFields hq) z.2 (r / 2)
  have hS : IsOpen S := isOpen_Ioo.prod (isOpen_horizontalBall G hq hqpos hspan z.2 (r / 2))
  have hzS : z ∈ S := by
    refine ⟨mem_inner_time_interiorCylinderTop hz.1.2 hr, ?_⟩
    rw [← hBall z.2 (r / 2)]
    exact Metric.mem_ball_self (α := CarnotPoint G hq hqpos hspan) (by positivity)
  have hmeasure : (volume : Measure (ℝ × (Fin N → ℝ))).restrict
      (Ioo (b - r ^ 2) b ×ˢ horizontalBall (G.horizontalFields hq) z.2 r) ≤
      volume.restrict (Ioo a T ×ˢ horizontalBall (G.horizontalFields hq) x₀ R) :=
    Measure.restrict_mono (prod_mono hItime hUspace) le_rfl
  have hnorm := eLpNorm_mono_measure (p := ENNReal.ofReal p) v hmeasure
  exact ⟨S, hS, hzS, hb.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hnorm))⟩

end HeatKernel
