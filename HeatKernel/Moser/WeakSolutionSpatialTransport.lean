-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionConvexEnergy

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Literal transport terms and localization of nonlinear weak tests -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The coefficient form is the sum of the coordinate flux integrals. -/
theorem coefficientEnergy_eq_sum_integral_flux {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a i j x‖ ≤ C)
    (z w : energyGraph (N := N) ⊤ X) :
    coefficientEnergy ⊤ X a z w = ∑ i, ∫ x,
      (∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x) *
        (w : GradientSpace (N := N) ⊤ q).snd i x := by
  have hi (i : Fin q) : Integrable (fun x => ∑ j,
      a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x *
        (w : GradientSpace (N := N) ⊤ q).snd i x) volume := by
    apply integrable_finsetSum
    intro j _
    have hz : MemLp ((z : GradientSpace (N := N) ⊤ q).snd j) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp ((z : GradientSpace (N := N) ⊤ q).snd j)
    have hw : MemLp ((w : GradientSpace (N := N) ⊤ q).snd i) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp ((w : GradientSpace (N := N) ⊤ q).snd i)
    exact (memLp_two_mul_of_ae_bound (ha i j) hz (hb i j)).integrable_mul hw
  unfold coefficientEnergy coefficientEnergyDensity
  simp only [Opens.coe_top, Measure.restrict_univ]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (Finset.sum_mul _ _ _).symm

/-- A localization cutoff equal to one on the weight and its gradient support
identifies the actual weak flux with the coefficient form of the cutoff curve. -/
theorem WeakSolutionSpatialWeight.flux_eq_coefficientEnergy_of_plateau {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a i j x‖ ≤ C)
    {u φ : (Fin N → ℝ) → ℝ} {g k : Fin q → (Fin N → ℝ) → ℝ}
    (z : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hflux : ∀ w, F w = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (φ x * (w : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (w : GradientSpace (N := N) ⊤ q).fst x))
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0) :
    F (W.energyMap hX T z) = coefficientEnergy ⊤ X a (zeroBoundaryEnergyInclusion V X z)
      (zeroBoundaryEnergyInclusion V X (W.energyMap hX T z)) := by
  rw [hflux, coefficientEnergy_eq_sum_integral_flux X a ha hb]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hgrad, W.energyMap_value_ae hX T z,
    W.energyMap_gradient_ae hX T z i] with x hx hv hg
  change (∑ j, a i j x * g j x) *
    (φ x * (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).snd i x +
      k i x * (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).fst x) =
    (∑ j, a i j x * (z : GradientSpace (N := N) ⊤ q).snd j x) *
      (W.energyMap hX T z : GradientSpace (N := N) ⊤ q).snd i x
  by_cases hactive : W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0)
  · obtain ⟨hφ, hk⟩ := hplateau x hactive
    have he (j : Fin q) : (z : GradientSpace (N := N) ⊤ q).snd j x = g j x := by
      simpa only [hφ, hk, mul_one, mul_zero, add_zero] using hx j
    simp only [hφ, hk, one_mul, zero_mul, add_zero, he]
  · have hw : W.toFun x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inl hn))
    have hd : W.gradient i x = 0 := not_ne_iff.mp (fun hn => hactive (Or.inr ⟨i, hn⟩))
    simp only [WeakSolutionSpatialWeight.energyMap] at hv hg ⊢
    simp only [hv, hg, hw, hd, zero_mul, add_zero, mul_zero]

end HeatKernel
