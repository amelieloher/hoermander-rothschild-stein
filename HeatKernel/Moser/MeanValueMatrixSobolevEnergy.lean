-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixMomentBudget
public import HeatKernel.Moser.MeanValueMatrixSobolevBudget
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Sobolev energy bounds for localized positive powers -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- The actual uniformly elliptic matrix time equation controls both the slice value
energy and the full spacetime Sobolev energy of a localized half-power. The
constant depends only on ellipticity, the cutoff derivatives and the power, and is independent
of the truncation height; no upper bound on the nonnegative value is needed. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.signed_matrix_positive_power_sobolev_energy_bounds
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b Ttime L M p ell upper : ℝ}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X
      coeff (Icc A B) u g φ k v F)
    (hcoeff_meas : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume)
    (hcoeff_sym : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ᵐ x ∂volume, ∀ i j, coeff t x i j = coeff t x j i)
    (hcoeff_elliptic : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ᵐ x ∂volume, ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ)
    (W S : WeakSolutionSpatialWeight V X)
    {η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1)
    (hL : 0 ≤ L) (hd : ∀ᵐ x ∂volume, (∑ i, d i x ^ 2) ≤ L)
    (hW : W.toFun =ᵐ[volume] η) (hWd : ∀ i, W.gradient i =ᵐ[volume] d i)
    (hS : S.toFun =ᵐ[volume] fun x => η x ^ 2)
    (hSd : ∀ i, S.gradient i =ᵐ[volume] fun x => 2 * η x * d i x)
    (hplateau : ∀ x, S.toFun x ≠ 0 ∨ (∃ i, S.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hM : 0 < M) (hp2 : 2 ≤ p)
    (hab : a < b) (hAa : A < a) (hbB : b < B)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hθa : θ a = 0)
    (hθunit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1)
    (hTtime : 0 ≤ Ttime) (hθderiv : ∀ t ∈ Icc a b, deriv θ t ≤ Ttime) :
    let H := fun t => (linearTailPowerWeakSolutionTest hM
      (show 1 ≤ p / 2 by linarith)).energyMap V X hX (v t)
    let w := fun t => θ t • W.multiplier (H t)
    let P := max p (p / ell)
    let Λ := max L (upper * L)
    let C := 2 * P * Ttime + (4 * P + 2) * Λ + 1
    let moment := ∫ t in Icc a b, ‖(H t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2
    MemLp w 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ C * moment) ∧
      (∫ t in Icc a b,
        ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
          ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤ C * moment := by
  dsimp only
  let χ := fun t => θ t ^ 2
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hχ : ContDiff ℝ 1 χ := hθ.pow 2
  have hχa : χ a = 0 := by simp only [χ, hθa, zero_pow (by decide : 2 ≠ 0)]
  have hχunit (t : ℝ) (ht : t ∈ Icc a b) : χ t ∈ Icc (0 : ℝ) 1 :=
    ⟨sq_nonneg _, by dsimp only [χ]; nlinarith [(hθunit t ht).1, (hθunit t ht).2]⟩
  have hχderiv (t : ℝ) (ht : t ∈ Icc a b) : deriv χ t ≤ 2 * Ttime :=
    deriv_sq_cutoff_le hθ (hθunit t ht) hTtime (hθderiv t ht)
  obtain ⟨hDi, hbudget, htotal⟩ := hp.signed_matrix_positive_power_budget_le_value_moment hX hell.le hupper
    hcoeff_meas hcoeff_sym hcoeff_elliptic S hη hηb
    hL hd hS hSd hplateau hM hp2 hab hAa hbB hχ hχa hχunit
    (show 0 ≤ 2 * Ttime by positivity) hχderiv
  exact W.signed_matrix_positive_power_sobolev_energy_bounds_of_budgets S hX
    (hp.1.mono_measure (Measure.restrict_mono hsub le_rfl)) hell hL
    hη hηb hd hW hWd hS hM hp2 hθ.continuous hθunit hTtime hDi hbudget htotal

end HeatKernel
