-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValuePowerEnergyRepresentatives
public import HeatKernel.Moser.MeanValueSquareCutoffEnergy
public import HeatKernel.Moser.MeanValueLocalizedGraphEnergy
public import HeatKernel.Moser.WeakSolutionConvexEnergy
import Mathlib.Tactic

/-! # Sobolev energy from truncated matrix power budgets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Terminal and total elliptic power budgets control the localized half-power
in the parabolic Sobolev energy norm. This implication uses only graph calculus,
and applies equally to solutions and subsolutions. -/
theorem WeakSolutionSpatialWeight.signed_matrix_positive_power_sobolev_energy_bounds_of_budgets
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W S : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {a b Ttime L M p ell upper : ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 (volume.restrict (Icc a b)))
    (hell : 0 < ell) (hL : 0 ≤ L)
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1)
    (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (hW : W.toFun =ᵐ[volume] η) (hWd : ∀ i, W.gradient i =ᵐ[volume] d i)
    (hS : S.toFun =ᵐ[volume] fun x => η x ^ 2)
    (hM : 0 < M) (hp2 : 2 ≤ p)
    {θ : ℝ → ℝ} (hθ : Continuous θ)
    (hθunit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1) (hTtime : 0 ≤ Ttime) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith only [hp2])).energyMap V X hX (v t)
    let E := fun t => S.energy
      (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith only [hp2])) (v t)
    let D := fun t => (ell / p) * coefficientEnergy ⊤ X
      (fun i j x => η x ^ 2 * if i = j then 1 else 0)
      (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))
    let moment := ∫ t in Icc a b, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2
    IntegrableOn D (Icc a b) →
    (∀ᵐ s ∂volume.restrict (Icc a b),
      θ s ^ 2 * E s + (∫ t in Icc a s, θ t ^ 2 * D t) ≤
        (2 * Ttime / 2 + 2 * upper * L) * moment) →
    ((∫ t in Icc a b, θ t ^ 2 * D t) ≤
      (2 * Ttime / 2 + 2 * upper * L) * moment) →
    let w := fun t => θ t • W.multiplier (H t)
    let P := max p (p / ell)
    let Λ := max L (upper * L)
    let C := 2 * P * Ttime + (4 * P + 2) * Λ + 1
    MemLp w 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ C * moment) ∧
      (∫ t in Icc a b,
        ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤ C * moment := by
  dsimp only
  intro hDi hbudget htotal
  let H := fun t => (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith only [hp2])).energyMap V X hX (v t)
  let Y := fun t => W.multiplier (H t)
  let m := fun t => ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2
  let E := fun t => S.energy
    (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith only [hp2])) (v t)
  let D := fun t => (ell / p) * coefficientEnergy ⊤ X
    (fun i j x => η x ^ 2 * if i = j then 1 else 0)
    (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))
  let P := max p (p / ell)
  let Λ := max L (upper * L)
  have hp0 : 0 < p := by linarith only [hp2]
  have hP : 0 < P := hp0.trans_le (le_max_left _ _)
  have hΛ : 0 ≤ Λ := hL.trans (le_max_left _ _)
  have hHv := (linearTailPowerWeakSolutionTest hM
    (show 1 ≤ p / 2 by linarith only [hp2])).memLp_energyMap V X hX hv
  have hY : MemLp Y 2 (volume.restrict (Icc a b)) := W.multiplier.comp_memLp' hHv
  have hD0 (t : ℝ) : 0 ≤ D t := by
    dsimp only [D]
    rw [square_weighted_identity_coefficientEnergy_eq_integral]
    exact mul_nonneg (by positivity)
      (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hm : IntegrableOn m (Icc a b) := by
    simpa only [IntegrableOn, m, H, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] using
      integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc a b)) hHv 0
  have hprimitive : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ P * E t := by
    filter_upwards [] with t
    have hb := W.cutoff_positive_half_power_slice_le_primitive S hX hW hS hM hp2 (v t)
    change _ ≤ p * E t at hb
    have he0 : 0 ≤ E t := by nlinarith [sq_nonneg ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he0)
  have hcut (t : ℝ) :
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t ∧
        ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
          2 * P * D t + 2 * Λ * m t := by
    obtain ⟨hvalue, hg⟩ := W.cutoff_identity_quadratic_energy_bounds
      hη hηb hW hWd hd hp0 (H t)
    refine ⟨hvalue, hg.trans ?_⟩
    have heq : 2 * p * ((1 / p) * coefficientEnergy ⊤ X
        (fun i j x => η x ^ 2 * if i = j then 1 else 0)
        (zeroBoundaryEnergyInclusion V X (H t)) (zeroBoundaryEnergyInclusion V X (H t))) =
        2 * (p / ell) * D t := by
      dsimp only [D]
      field_simp
    rw [heq]
    have hdle := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right p (p / ell)) (by norm_num : (0 : ℝ) ≤ 2))
      (hD0 t)
    have hmle := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left L (upper * L)) (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg ‖(H t : GradientSpace (N := N) ⊤ q).fst‖)
    exact add_le_add hdle hmle
  have hC : (2 * Ttime / 2 + 2 * upper * L) ≤ (2 * Ttime / 2 + 2 * Λ) := by
    have hh := le_max_right L (upper * L)
    dsimp only [Λ]
    nlinarith only [hh]
  have hbudget' : ∀ᵐ t ∂volume.restrict (Icc a b),
      θ t ^ 2 * E t + (∫ s in Icc a t, θ s ^ 2 * D s) ≤
        (2 * Ttime / 2 + 2 * Λ) * (∫ s in Icc a b, m s) := by
    filter_upwards [hbudget] with t ht
    exact ht.trans (mul_le_mul_of_nonneg_right hC (integral_nonneg fun _ => sq_nonneg _))
  have htotal' : (∫ t in Icc a b, θ t ^ 2 * D t) ≤
      (2 * Ttime / 2 + 2 * Λ) * (∫ s in Icc a b, m s) :=
    htotal.trans (mul_le_mul_of_nonneg_right hC (integral_nonneg fun _ => sq_nonneg _))
  have hbound := localized_graph_sobolev_energy_bounds (T := 2 * Ttime) hP
    (show 0 ≤ 2 * Ttime by positivity) hΛ hY hθ hθunit hDi hD0 hm
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hprimitive
    (Filter.Eventually.of_forall fun t => (hcut t).1)
    (Filter.Eventually.of_forall fun t => (hcut t).2) hbudget' htotal'
  simpa only [show P * (2 * Ttime) = 2 * P * Ttime by ring] using hbound

end HeatKernel
