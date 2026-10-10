-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ExponentialMultipliers
public import HeatKernel.Gaussian.ExponentialOperator

/-! # Exponential form products identified with their L² multipliers -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace RothschildStein
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

theorem exists_horizontalExponentialFormProduct
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (ψ : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hψ : MemLocalEnergy ⊤ X ψ) (hw : ∀ i, hasWeakWordDeriv X ⊤ [i] ψ (g i))
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) {D : ℝ} (hD : 0 ≤ D)
    (hg : ∀ i, ∀ᵐ x ∂volume, ‖g i x‖ ≤ D) (a : ℝ) (u : energyGraph ⊤ X) :
    ∃ w : energyGraph ⊤ X,
      energyInclusion ⊤ X w =
        Gaussian.exponentialMultiplication (volume.restrict (univ : Set (Fin N → ℝ)))
          ψ hψ.1 B hB a (energyInclusion ⊤ X u) ∧
      ∀ i, (w : GradientSpace ⊤ q).snd i
        =ᵐ[volume.restrict (univ : Set (Fin N → ℝ))] fun x =>
          Real.exp (a * ψ x) *
            ((u : GradientSpace ⊤ q).snd i x + a * energyInclusion ⊤ X u x * g i x) := by
  have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB 0)
  have hb : ∀ᵐ x ∂volume, ‖ψ x‖ ≤ B :=
    Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x)
  obtain ⟨w, hwf, hwg⟩ := exists_energyGraph_mul_exp_bounded_local X hX u hψ hw
    hB0 hD hb hg a
  refine ⟨w, ?_, fun i => ?_⟩
  · apply Lp.ext
    have hm := Gaussian.coeFn_exponentialMultiplication
      (volume.restrict (univ : Set (Fin N → ℝ))) ψ hψ.1 B hB a (energyInclusion ⊤ X u)
    simp only [Opens.coe_top, Measure.restrict_univ] at hm ⊢
    exact hwf.trans hm.symm
  · simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [hwg i] with x hx
    rw [hx]
    change Real.exp (a * ψ x) * (u : GradientSpace ⊤ q).snd i x +
        (a * Real.exp (a * ψ x) * g i x) * (u : GradientSpace ⊤ q).fst x =
      Real.exp (a * ψ x) *
        ((u : GradientSpace ⊤ q).snd i x + a * (u : GradientSpace ⊤ q).fst x * g i x)
    ring

end HeatKernel
