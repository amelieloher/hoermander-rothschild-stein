-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.CompactLocalGradient
public import RothschildStein.H3.RelcompactOpenExhaustion
public import RothschildStein.P2.SmoothingGlue
import Mathlib.Tactic

/-! # Compatible weak gradients on open local energy domains -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Local energy membership supplies one weak gradient on the whole open domain.
Its components are square integrable on compact subsets and agree with every
local global-form representative. -/
theorem MemLocalEnergy.exists_weak_gradient_on_open {N q : ℕ}
    {U : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    ∃ g : Fin q → (Fin N → ℝ) → ℝ,
      (∀ i, hasWeakWordDeriv X U [i] f (g i)) ∧
      (∀ K : Set (Fin N → ℝ), IsCompact K → K ⊆ U →
        ∀ i, MemLp (g i) 2 (volume.restrict K)) ∧
      ∀ (V : Opens (Fin N → ℝ)), V ≤ U →
        ∀ v : energyGraph (N := N) ⊤ X,
          energyInclusion ⊤ X v =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] f →
          ∀ i, energyGradient ⊤ X v i =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] g i := by
  classical
  have hs := hf.memSobolevXLoc hX
  have hi := H3.locallyIntegrableOn_of_memSobolevXLoc noDriftWeight X U 1 2
    (by norm_num) hs
  obtain ⟨V, _, hV, hcover, _⟩ := H3.exists_relcompact_open_exhaustion U
  have hlocal := fun n => (exists_horizontal_derivatives_of_memSobolevXLoc hs
    (hV n).1 ((hV n).2.1.trans (hV (n + 1)).2.2)).2
  choose g hg using hlocal
  have hglue := fun i => P2.exists_hasWeakWordDeriv_gluing X U
    (fun j => (hX j).contDiffOn) [i] hi V (fun n => (hV n).2.2)
    hcover (fun n => g n i) (fun n => (hg n i).1)
  choose G hG using hglue
  refine ⟨G, fun i => (hG i).1, ?_, ?_⟩
  · intro K hK hKU i
    exact hf.memLp_weak_gradient_restrict_compact U X hX i (hG i).1 hK hKU
  · intro W hWU v hv i
    exact energyGradient_eq_of_local_weak_derivative U W hWU X hX v hv i (hG i).1

end HeatKernel
