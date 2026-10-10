-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.WeakCutoffSupport
public import HeatKernel.Form.BoundedEnergyMultiplication
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! Bounded weak spatial cutoffs of energy curves localized by a smooth plateau. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein Filter
open scoped ENNReal
namespace HeatKernel

/-- Multiplying a plateau-localized energy curve by a bounded weak cutoff
produces the literal cutoff value and the Leibniz gradient with the original
weak gradient of the underlying function. -/
theorem exists_weak_cutoff_energy_curve_of_plateau {N q : ℕ}
    {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {φ ψ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    (hφ : MemLocalEnergy ⊤ X φ) (hk : ∀ i, hasWeakWordDeriv X ⊤ [i] φ (k i))
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ᵐ x ∂volume, ‖φ x‖ ≤ C) (hkb : ∀ i, ∀ᵐ x ∂volume, ‖k i x‖ ≤ L)
    {P : Set (Fin N → ℝ)} (hP : IsOpen P) (hs : tsupport φ ⊆ P)
    (hψ : EqOn ψ (fun _ => 1) P)
    (u : T → (Fin N → ℝ) → ℝ) (g : Fin q → T → (Fin N → ℝ) → ℝ)
    (v : T → energyGraph (N := N) ⊤ X) (hv : MemLp v 2 μ)
    (hval : ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * ψ x)
    (hgrad : ∀ i, ∀ᵐ t ∂μ, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i t x * ψ x + u t x * fieldDerivative (X i) ψ x) :
    ∃ z : T → energyGraph (N := N) ⊤ X, MemLp z 2 μ ∧
      (∀ᵐ t ∂μ, (z t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        fun x => u t x * φ x) ∧
      ∀ i, ∀ᵐ t ∂μ, (z t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        fun x => g i t x * φ x + u t x * k i x := by
  obtain ⟨M, hM⟩ := exists_energyMultiplierLinearMap X hX hφ hk hC hL hb hkb
  refine ⟨fun t => M (v t), hv.continuousLinearMap_comp (𝕜 := ℝ) M, ?_, ?_⟩
  · filter_upwards [hval] with t ht
    have hm := (hM (v t)).1
    change (M (v t) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] _ at hm
    simp only [energyInclusion_apply] at hm
    filter_upwards [hm, ht] with x hx htx
    rw [hx, htx]
    by_cases hp : x ∈ P
    · rw [hψ hp]
      ring
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hp (hs hh))
      simp only [hz, zero_mul, mul_zero]
  · intro i
    have hkzero := hasWeakWordDeriv_ae_zero_outside_tsupport X [i] (hk i)
    filter_upwards [hval, hgrad i] with t ht hgt
    have hm := (hM (v t)).2 i
    change (M (v t) : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] _ at hm
    simp only [energyInclusion_apply, energyGradient_apply] at hm
    filter_upwards [hm, ht, hgt, hkzero] with x hx htx hgtx hkx
    rw [hx, htx, hgtx]
    by_cases hp : x ∈ P
    · rw [hψ hp, fieldDerivative_eq_zero_on_plateau (X i) hP hψ hp]
      ring
    · have hxs : x ∉ tsupport φ := fun hh => hp (hs hh)
      rw [image_eq_zero_of_notMem_tsupport hxs, hkx hxs]
      ring

end HeatKernel
