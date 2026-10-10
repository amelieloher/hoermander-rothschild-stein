-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLocalizedEnergyBounds
public import HeatKernel.Moser.MeanValueEnergyIntegrability
public import HeatKernel.Moser.MeanValueIdentityEnergyBudget
public import HeatKernel.Moser.MeanValueSquareCutoffEnergy
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Temporal localization of graph-valued energy budgets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The complete cutoff quadratic energy can be written using the square-weighted
identity form, with the reciprocal power used in the dissipation budget. -/
theorem WeakSolutionSpatialWeight.cutoff_identity_quadratic_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X)
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ} {L p : ℝ}
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1)
    (hW : W.toFun =ᵐ[volume] η) (hWd : ∀ i, W.gradient i =ᵐ[volume] d i)
    (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L) (hp : 0 < p)
    (z : zeroBoundaryGraph V X) :
    ‖(W.multiplier z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
        ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∧
      ‖(W.multiplier z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
        2 * p * ((1 / p) * coefficientEnergy ⊤ X
          (fun i j x => η x ^ 2 * if i = j then 1 else 0)
          (zeroBoundaryEnergyInclusion V X z) (zeroBoundaryEnergyInclusion V X z)) +
            2 * L * ‖(z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 := by
  obtain ⟨hv, hg⟩ := W.cutoff_quadratic_energy_bounds hη hηb hW hWd hd z
  refine ⟨hv, ?_⟩
  rw [square_weighted_identity_coefficientEnergy_eq_integral]
  have hinc : (zeroBoundaryEnergyInclusion V X z : GradientSpace (N := N) ⊤ q) =
      (z : GradientSpace (N := N) ⊤ q) := rfl
  rw [hinc]
  convert hg using 1
  field_simp

/-- A graph curve with primitive and gradient comparisons inherits slice and
integrated Sobolev energy bounds after temporal localization. The comparisons
and the two primitive budgets are explicit hypotheses. -/
theorem localized_graph_sobolev_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a b p T L : ℝ} (hp : 0 < p) (hT : 0 ≤ T) (hL : 0 ≤ L)
    {Y : ℝ → zeroBoundaryGraph V X} (hY : MemLp Y 2 (volume.restrict (Icc a b)))
    {θ : ℝ → ℝ} (hθ : Continuous θ)
    (hθunit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1)
    {E D m : ℝ → ℝ} (hD : IntegrableOn D (Icc a b))
    (hD0 : ∀ t, 0 ≤ D t) (hm : IntegrableOn m (Icc a b))
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hprimitive : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ p * E t)
    (hvalue : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t)
    (hgradient : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ 2 * p * D t + 2 * L * m t)
    (hbudget : ∀ᵐ t ∂volume.restrict (Icc a b),
      θ t ^ 2 * E t + (∫ s in Icc a t, θ s ^ 2 * D s) ≤
        (T / 2 + 2 * L) * (∫ s in Icc a b, m s))
    (htotal : (∫ t in Icc a b, θ t ^ 2 * D t) ≤
      (T / 2 + 2 * L) * (∫ t in Icc a b, m t)) :
    let w := fun t => θ t • Y t
    MemLp w 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
          (p * T + (4 * p + 2) * L + 1) * (∫ s in Icc a b, m s)) ∧
      (∫ t in Icc a b, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤
          (p * T + (4 * p + 2) * L + 1) * (∫ t in Icc a b, m t) := by
  dsimp only
  let w := fun t => θ t • Y t
  have hw : MemLp w 2 (volume.restrict (Icc a b)) := by
    apply hY.mono (hθ.aestronglyMeasurable.smul hY.aestronglyMeasurable)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    change ‖θ t • Y t‖ ≤ ‖Y t‖
    rw [norm_smul, Real.norm_of_nonneg (hθunit t ht).1]
    exact (mul_le_mul_of_nonneg_right (hθunit t ht).2 (norm_nonneg _)).trans_eq (one_mul _)
  have hχunit (t : ℝ) (ht : t ∈ Icc a b) : θ t ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by nlinarith [(hθunit t ht).1, (hθunit t ht).2]⟩
  have hnorms (t : ℝ) :
      ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
          θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∧
        ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 =
          θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 := by
    dsimp only [w]
    simp only [Submodule.coe_smul, WithLp.smul_fst, WithLp.smul_snd,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, and_self]
  have henergyEq (t : ℝ) :
      ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
          θ t ^ 2 * (‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
            ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by
    rw [(hnorms t).1, (hnorms t).2, mul_add]
  have hwi : IntegrableOn (fun t => θ t ^ 2 *
      (‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2)) (Icc a b) := by
    have hi := integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc a b)) hw 1
    simpa only [IntegrableOn, one_pow, one_mul, henergyEq] using hi
  have heq : (p * T / 2) / p = T / 2 := by field_simp
  rw [← heq] at hbudget htotal
  have hslice := ae_localized_value_energy_le_of_primitive_budget (H := p * T / 2) hp
    (fun t ht => (hχunit t ht).1) hD0 hprimitive hbudget
  have henergy := integral_localized_sobolev_energy_le_of_dissipation_budget (H := p * T / 2) hp hL
    (hθ.pow 2) hχunit hD hm hm0 hwi hvalue hgradient htotal
  refine ⟨hw, ?_, ?_⟩
  · filter_upwards [hslice] with t ht
    rw [(hnorms t).1]
    apply ht.trans
    apply mul_le_mul_of_nonneg_right ?_ (integral_nonneg_of_ae hm0)
    nlinarith only [mul_nonneg hp.le hT, hL, mul_nonneg hp.le hL]
  · change (∫ t in Icc a b, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤ _
    simp_rw [henergyEq]
    simpa only [Pi.pow_apply, show 2 * (p * T / 2) = p * T by ring] using henergy

end HeatKernel
