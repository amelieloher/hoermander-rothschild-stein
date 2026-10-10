-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CompactExponential
public import HeatKernel.Form.LocalEnergyAlgebra
public import HeatKernel.Form.LocalLipschitzCalculus
public import HeatKernel.Form.ContinuouslyDifferentiableComposition
public import HeatKernel.Form.StrongLocality
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Ring

/-! # Exponentials of bounded local horizontal energy functions -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped NNReal

namespace HeatKernel

/-- A bounded local energy function has a local energy exponential. -/
theorem MemLocalEnergy.exp_bounded {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ψ : (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy U X ψ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖ψ x‖ ≤ A) (α : ℝ) :
    MemLocalEnergy U X (fun x => Real.exp (α * ψ x)) := by
  obtain ⟨η, hη, hc, hzero, he⟩ := exists_compact_exponential α hA
  obtain ⟨C, hC⟩ := hc.deriv.exists_bound_of_continuous (hη.continuous_deriv (by simp))
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hLip : LipschitzWith ⟨C, hCp⟩ η := lipschitzWith_of_nnnorm_deriv_le
    (hη.differentiable (by simp)) (fun s => by exact_mod_cast hC s)
  have H := (hψ.comp_lipschitz U X hX hLip hzero).add U X
    (memLocalEnergy_of_contDiff U X hX (contDiff_const (c := (1 : ℝ))))
  apply H.congr_ae U X
  filter_upwards [hb] with x hx
  simp only [Pi.add_apply, Function.comp_apply, (he (ψ x) hx).1]
  ring

/-- The local energy representative of a bounded exponential has the expected horizontal
chain rule on every relatively compact open patch. -/
theorem MemLocalEnergy.exists_exp_bounded_gradient {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {ψ : (Fin N → ℝ) → ℝ}
    (hψ : MemLocalEnergy U X ψ) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖ψ x‖ ≤ A) (α : ℝ)
    (V : Opens (Fin N → ℝ)) (hVc : IsCompact (closure (V : Set (Fin N → ℝ))))
    (hVU : closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ))) :
    ∃ w z : energyGraph (N := N) ⊤ X,
      ((w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] ψ) ∧
      ((z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
        (fun x => Real.exp (α * ψ x))) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
        (fun x => α * Real.exp (α * ψ x) * (w : GradientSpace (N := N) ⊤ q).snd i x) := by
  obtain ⟨η, hη, hc, hzero, he⟩ := exists_compact_exponential α hA
  obtain ⟨C, hC⟩ := hc.deriv.exists_bound_of_continuous (hη.continuous_deriv (by simp))
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  obtain ⟨w, hw⟩ := hψ.2 V hVc hVU
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_comp_contDiff_one X hX w
    (hη.of_le (by simp)) hzero (C := ⟨C, hCp⟩) hC
  obtain ⟨c, hcf⟩ := (memLocalEnergy_of_contDiff U X hX
    (contDiff_const (c := (1 : ℝ)))).2 V hVc hVU
  have hcg := energyGraph_gradient_zero_on_of_fst_const V X hX c 1 hcf
  have hbV := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVU) hb
  have hsumf : ((z + c : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => (z : GradientSpace (N := N) ⊤ q).fst x + (c : GradientSpace (N := N) ⊤ q).fst x) := by
    simpa only [Submodule.coe_add, WithLp.add_fst, Pi.add_def, Opens.coe_top, Measure.restrict_univ]
      using Lp.coeFn_add (z : GradientSpace (N := N) ⊤ q).fst (c : GradientSpace (N := N) ⊤ q).fst
  refine ⟨w, z + c, hw, ?_, fun i => ?_⟩
  · filter_upwards [ae_restrict_of_ae hsumf, ae_restrict_of_ae hzf, hw, hcf, hbV]
      with x hx hz hwx hcx hbx
    rw [hx, hz, hwx, hcx, (he (ψ x) hbx).1]
    ring
  · have hsumg : ((z + c : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => (z : GradientSpace (N := N) ⊤ q).snd i x + (c : GradientSpace (N := N) ⊤ q).snd i x) := by
      simpa only [Submodule.coe_add, WithLp.add_snd, PiLp.add_apply, Pi.add_def,
        Opens.coe_top, Measure.restrict_univ] using
        Lp.coeFn_add ((z : GradientSpace (N := N) ⊤ q).snd i) ((c : GradientSpace (N := N) ⊤ q).snd i)
    filter_upwards [ae_restrict_of_ae hsumg, ae_restrict_of_ae (hzg i), hw, hcg i, hbV]
      with x hx hz hwx hcx hbx
    rw [hx, hz, hwx, hcx, (he (ψ x) hbx).2, add_zero]



end HeatKernel
