-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalScalarComposition
public import HeatKernel.Form.CountableExceptionalChainRule
public import HeatKernel.Form.StrongLocality
import Mathlib.Tactic.Linter

/-! # Local horizontal chain rules with countable exceptional scalar levels -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- On every relatively compact patch a Lipschitz composition that is locally C¹ off
countably many levels has the exact weak-gradient chain rule, with any value at zero. -/
theorem MemLocalEnergy.exists_comp_contDiffAt_off_countable_gradient {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) {η d : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C η)
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)
    (hd : ∀ s ∉ S, d s = deriv η s)
    (V : Opens (Fin N → ℝ)) (hVc : IsCompact (closure (V : Set (Fin N → ℝ))))
    (hVU : closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ))) :
    ∃ w z : energyGraph (N := N) ⊤ X,
      ((w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f) ∧
      ((z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] η ∘ f) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
        fun x => d (f x) * (w : GradientSpace (N := N) ⊤ q).snd i x := by
  let ψ : ℝ → ℝ := fun s => η s - η 0
  have hψ : LipschitzWith C ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ, dist_sub_right] using hLip.dist_le_mul x y
  have hzero : ψ 0 = 0 := sub_self _
  have hψlocal : ∀ s ∉ S, ContDiffAt ℝ 1 ψ s := fun s hs => (hη s hs).sub contDiffAt_const
  have hψd : ∀ s ∉ S, d s = deriv ψ s := fun s hs =>
    (hd s hs).trans (((hη s hs).differentiableAt_one.hasDerivAt.sub_const (η 0)).deriv.symm)
  obtain ⟨w, hw⟩ := hf.2 V hVc hVU
  obtain ⟨z, hzf, hzg, _⟩ := exists_energyGraph_comp_contDiffAt_off_countable X hX w hψ hzero S hS hψlocal hψd
  obtain ⟨c, hcf⟩ := (memLocalEnergy_of_contDiff U X hX
    (contDiff_const (c := η 0))).2 V hVc hVU
  have hcg := energyGraph_gradient_zero_on_of_fst_const V X hX c (η 0) hcf
  have hsumf : ((z + c : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => (z : GradientSpace (N := N) ⊤ q).fst x + (c : GradientSpace (N := N) ⊤ q).fst x) := by
    simpa only [Submodule.coe_add, WithLp.add_fst, Pi.add_def, Opens.coe_top, Measure.restrict_univ]
      using Lp.coeFn_add (z : GradientSpace (N := N) ⊤ q).fst (c : GradientSpace (N := N) ⊤ q).fst
  refine ⟨w, z + c, hw, ?_, fun i => ?_⟩
  · filter_upwards [ae_restrict_of_ae hsumf, ae_restrict_of_ae hzf, hw, hcf] with x hx hz hwx hcx
    rw [hx, hz, hwx, hcx]
    simp only [ψ, sub_add_cancel, Function.comp_apply]
  · have hsumg : ((z + c : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => (z : GradientSpace (N := N) ⊤ q).snd i x + (c : GradientSpace (N := N) ⊤ q).snd i x) := by
      simpa only [Submodule.coe_add, WithLp.add_snd, PiLp.add_apply, Pi.add_def,
        Opens.coe_top, Measure.restrict_univ] using
        Lp.coeFn_add ((z : GradientSpace (N := N) ⊤ q).snd i) ((c : GradientSpace (N := N) ⊤ q).snd i)
    filter_upwards [ae_restrict_of_ae hsumg, ae_restrict_of_ae (hzg i), hw, hcg i]
      with x hx hz hwx hcx
    rw [hx, hz, hwx, hcx, add_zero]



end HeatKernel
