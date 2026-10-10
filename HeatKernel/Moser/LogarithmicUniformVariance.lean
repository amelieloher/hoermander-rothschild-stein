-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.UniformLocalTentPoincare
public import HeatKernel.Bridge.LocalShiftedGradients
public import HeatKernel.Moser.LogarithmicMatrixVariance
public import Mathlib.MeasureTheory.Measure.CompleteLattice
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform matrix-energy variance for centered shifted logarithms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric TopologicalSpace RothschildStein
namespace HeatKernel

/-- The uniform tent Poincaré constant controls the centered shifted logarithm
by its literal matrix energy, on every strictly interior concentric ball. -/
theorem exists_uniform_logarithmic_matrix_tent_variance {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (x : CarnotPoint G hq hqpos hspan) (ρ R : ℝ), 0 < ρ → ρ < R →
    ∀ (u : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ),
    let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x R,
      isOpen_horizontalBall G hq hqpos hspan x R⟩
    MemLocalEnergy U (G.horizontalFields hq) u →
    (∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] u (g i)) →
    (∀ᵐ y ∂volume.restrict (U : Set (Fin N → ℝ)), 0 ≤ u y) →
    (∀ i, AEStronglyMeasurable (fun y : CarnotPoint G hq hqpos hspan => g i y)
      ((CarnotPoint.volume G hq hqpos hspan).restrict (ball x R))) →
    ∀ (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) (ell upper ε : ℝ), 0 < ell → 0 < ε →
    (∀ i j, Measurable (a i j)) →
    (∀ᵐ y ∂volume, ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j y) ξ ∧
      matrixEnergy (fun i j => a i j y) ξ ≤ upper * coordinateNormSq ξ) →
    let w := fun y : CarnotPoint G hq hqpos hspan => max (1 - dist x y / ρ) 0 ^ 2
    let f := fun y : CarnotPoint G hq hqpos hspan => Real.log (u y + ε) - Real.log ε
    let m := (∫ y, w y * f y ∂CarnotPoint.volume G hq hqpos hspan) /
      (∫ y, w y ∂CarnotPoint.volume G hq hqpos hspan)
    Integrable (fun y => w y * (f y - m)^2) (CarnotPoint.volume G hq hqpos hspan) ∧
    (∫ y, w y * (f y - m)^2 ∂CarnotPoint.volume G hq hqpos hspan) ≤
      (K * ρ^2 / ell) * ∫ y, ∑ i, ∑ j, a i j y *
        (max (1 - dist x y / ρ) 0 * ((u y + ε)⁻¹ * g j y)) *
        (max (1 - dist x y / ρ) 0 * ((u y + ε)⁻¹ * g i y))
          ∂CarnotPoint.volume G hq hqpos hspan := by
  obtain ⟨P, hP, htent⟩ := CarnotPoint.exists_uniform_local_energy_tent_constant G hq hqpos hspan hw
  refine ⟨P * ((2 : ℝ)^G.homogeneousDimension + 7/4), by positivity, ?_⟩
  intro x ρ R hρ hρR u g U hu hg hn hgm a ell upper ε hell hε ha hquad
  let V := ball x ρ
  let w := fun y : CarnotPoint G hq hqpos hspan => max (1 - dist x y / ρ) 0 ^ 2
  let f := fun y : CarnotPoint G hq hqpos hspan => Real.log (u y + ε) - Real.log ε
  let d := fun i (y : CarnotPoint G hq hqpos hspan) => g i y / (u y + ε)
  obtain ⟨hl, hdl⟩ := hu.log_add_const_with_weak_gradient (G.horizontalFields_contDiff hq) hg hn hε
  obtain ⟨hf, hdf⟩ := hl.add_const_with_weak_gradient
    (G.horizontalFields_contDiff hq) hdl (-Real.log ε)
  have hf' : MemLocalEnergy U (G.horizontalFields hq) f := by
    change MemLocalEnergy U (G.horizontalFields hq)
      (fun y : Fin N → ℝ => Real.log (u y + ε) - Real.log ε)
    simpa only [sub_eq_add_neg] using hf
  have hdf' : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] f (d i) := by
    intro i
    change hasWeakWordDeriv (G.horizontalFields hq) U [i]
      (fun y : Fin N → ℝ => Real.log (u y + ε) - Real.log ε)
      (fun y => g i y / (u y + ε))
    simpa only [sub_eq_add_neg] using hdf i
  have hroom : {y : Fin N → ℝ | horizontalL2Distance (G.horizontalFields hq) x y ≤
      ENNReal.ofReal ρ} ⊆ U := by
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hρ.trans hρR)).mpr hρR)
  obtain ⟨hvar, hgrad⟩ := CarnotPoint.integrable_local_tent_energy_moments G hq hqpos hspan hw
    x hρ U hroom f d hf' hdf' (by norm_num : 0 < (2 : ℕ))
  have hz (y : CarnotPoint G hq hqpos hspan) (hy : y ∉ V) : w y = 0 := by
    have hd : ρ ≤ dist x y := by simpa only [V, mem_ball, not_lt, dist_comm y x] using hy
    have hh : 1 ≤ dist x y / ρ := (le_div_iff₀ hρ).mpr (by simpa using hd)
    simp only [w, max_eq_right (by linarith : 1 - dist x y / ρ ≤ 0), zero_pow (by decide : 2 ≠ 0)]
  have hfull (F : CarnotPoint G hq hqpos hspan → ℝ) :
      (∫ y in V, w y * F y ∂CarnotPoint.volume G hq hqpos hspan) =
        ∫ y, w y * F y ∂CarnotPoint.volume G hq hqpos hspan := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hz y hy, zero_mul]
  have hv := htent x ρ R hρ hρR f hf' d hdf' 2 (Or.inr rfl)
  change (∫ y in V, w y * (f y -
    (∫ y in V, w y * f y ∂CarnotPoint.volume G hq hqpos hspan) /
    (∫ y, w y ∂CarnotPoint.volume G hq hqpos hspan))^2 ∂CarnotPoint.volume G hq hqpos hspan) ≤
    (P * ((2 : ℝ)^G.homogeneousDimension + 7/4)) * ρ^2 *
      ∫ y in V, w y * ∑ i, (d i y)^2 ∂CarnotPoint.volume G hq hqpos hspan at hv
  rw [hfull, hfull, hfull] at hv
  let ν := (CarnotPoint.volume G hq hqpos hspan).restrict V
  have hVU : V ⊆ ball x R := ball_subset_ball hρR.le
  have hum : AEStronglyMeasurable (fun y : CarnotPoint G hq hqpos hspan => u y)
      ((CarnotPoint.volume G hq hqpos hspan).restrict (ball x R)) := by
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
    exact hu.1
  have hdm (i : Fin q) : AEStronglyMeasurable (d i) ν := by
    simpa only [d, div_eq_mul_inv] using
      ((hgm i).mono_measure (Measure.restrict_mono hVU le_rfl)).fun_mul
        (((hum.mono_measure (Measure.restrict_mono hVU le_rfl)).fun_add
          aestronglyMeasurable_const).fun_inv₀)
  obtain ⟨hmat, hb⟩ := logarithmic_variance_le_matrix_energy (a := fun i j (y : CarnotPoint G hq hqpos hspan) => a i j y) (f := f)
    (m := (∫ y, w y * f y ∂CarnotPoint.volume G hq hqpos hspan) /
      (∫ y, w y ∂CarnotPoint.volume G hq hqpos hspan)) hell
    (by positivity : 0 ≤ (P * ((2 : ℝ)^G.homogeneousDimension + 7/4)) * ρ^2)
    (show AEStronglyMeasurable w ν from (show Continuous w by fun_prop).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => sq_nonneg _)
    (fun i j => (show Measurable (fun y : CarnotPoint G hq hqpos hspan => a i j y) from ha i j).aestronglyMeasurable) hdm hgrad.integrableOn
    (ae_restrict_of_ae (show ∀ᵐ y ∂CarnotPoint.volume G hq hqpos hspan,
      ell * coordinateNormSq (fun i => d i y) ≤ matrixEnergy (fun i j => a i j y) (fun i => d i y) ∧
      matrixEnergy (fun i j => a i j y) (fun i => d i y) ≤ upper * coordinateNormSq (fun i => d i y)
      from hquad.mono fun y hy => hy (fun i => d i y))) (by
      change (∫ y in V, w y * (f y -
        (∫ y, w y * f y ∂CarnotPoint.volume G hq hqpos hspan) /
          (∫ y, w y ∂CarnotPoint.volume G hq hqpos hspan))^2 ∂CarnotPoint.volume G hq hqpos hspan) ≤
        _ * ∫ y in V, w y * ∑ i, (d i y)^2 ∂CarnotPoint.volume G hq hqpos hspan
      rw [hfull, hfull]
      exact hv)
  have henergy : (∫ y in V, w y * matrixEnergy (fun i j => a i j y) (fun i => d i y)
      ∂CarnotPoint.volume G hq hqpos hspan) =
      ∫ y, ∑ i, ∑ j, a i j y *
        (max (1 - dist x y / ρ) 0 * ((u y + ε)⁻¹ * g j y)) *
        (max (1 - dist x y / ρ) 0 * ((u y + ε)⁻¹ * g i y))
          ∂CarnotPoint.volume G hq hqpos hspan := by
    rw [hfull]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [w, matrixEnergy, d, Finset.mul_sum, div_eq_mul_inv, pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  change (∫ y in V, w y * (f y -
    (∫ y, w y * f y ∂CarnotPoint.volume G hq hqpos hspan) /
      (∫ y, w y ∂CarnotPoint.volume G hq hqpos hspan))^2 ∂CarnotPoint.volume G hq hqpos hspan) ≤
    _ * (∫ y in V, w y * matrixEnergy (fun i j => a i j y) (fun i => d i y)
      ∂CarnotPoint.volume G hq hqpos hspan) at hb
  rw [hfull, henergy] at hb
  exact ⟨hvar _, hb⟩

end HeatKernel
