-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalExceptionalComposition
public import HeatKernel.Bridge.LocalWeakGradientWitness
import Mathlib.Tactic.Linter

/-! # Scalar chain rules for specified local weak gradients -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped NNReal
namespace HeatKernel

/-- A Lipschitz scalar map that is C¹ away from countably many levels preserves
local energy membership and has the chain derivative for every supplied weak gradient.
The derivative factor may be assigned arbitrary values at exceptional levels. -/
theorem MemLocalEnergy.comp_piecewise_with_weak_gradient {N q : ℕ}
    {U : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    {g : Fin q → (Fin N → ℝ) → ℝ} (hg : ∀ i, hasWeakWordDeriv X U [i] f (g i))
    {η d : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C η)
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)
    (hd : ∀ s ∉ S, d s = deriv η s) :
    MemLocalEnergy U X (η ∘ f) ∧
      ∀ i, hasWeakWordDeriv X U [i] (η ∘ f) (fun x => d (f x) * g i x) := by
  have hc := hf.comp_lipschitz_scalar U X hX hLip
  obtain ⟨G, hG, _, _⟩ := hc.exists_weak_gradient_on_open hX
  obtain ⟨V, _, hV, hcover, _⟩ := H3.exists_relcompact_open_exhaustion U
  have hpatch : ∀ n i, G i =ᵐ[volume.restrict (V n : Set (Fin N → ℝ))]
      (fun x => d (f x) * g i x) := by
    intro n i
    have hVU : closure (V n : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)) :=
      (hV n).2.1.trans (hV (n + 1)).2.2
    obtain ⟨w, z, hw, hz, hzg⟩ :=
      hf.exists_comp_contDiffAt_off_countable_gradient U X hX hLip S hS hη hd
        (V n) (hV n).1 hVU
    have hwg := energyGradient_eq_of_local_weak_derivative U (V n) (hV n).2.2
      X hX w hw i (hg i)
    have hzg' := energyGradient_eq_of_local_weak_derivative U (V n) (hV n).2.2
      X hX z hz i (hG i)
    change (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[_] g i at hwg
    change (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[_] G i at hzg'
    exact hzg'.symm.trans ((hzg i).trans (hwg.mono fun x hx => congrArg (fun y => d (f x) * y) hx))
  refine ⟨hc, fun i => ?_⟩
  have heq : G i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      (fun x => d (f x) * g i x) := by
    change ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), G i x = d (f x) * g i x
    rw [ae_restrict_iff' U.isOpen.measurableSet]
    have hall := (ae_all_iff).mpr (fun n => ae_imp_of_ae_restrict (hpatch n i))
    filter_upwards [hall] with x hx hxU
    obtain ⟨n, hn⟩ := hcover x hxU
    exact hx n hn
  exact RothschildStein.S.hasWeakWordDeriv_congr_ae X U (hG i) ae_eq_rfl heq

end HeatKernel
