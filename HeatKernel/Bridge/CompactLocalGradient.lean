-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalSobolev
import Mathlib.Tactic.Linter

/-! # Compact square integrability of supplied local weak gradients -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Every supplied weak gradient of a local energy function is square integrable
on compact subsets of its domain, by uniqueness against a global form representative. -/
theorem MemLocalEnergy.memLp_weak_gradient_restrict_compact {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f g : (Fin N → ℝ) → ℝ} (hf : MemLocalEnergy U X f)
    (i : Fin q) (hg : hasWeakWordDeriv X U [i] f g)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ))) :
    MemLp g 2 (volume.restrict K) := by
  obtain ⟨V, hKV, hVc, hVU⟩ := exists_precompact_open_of_isCompact U hK hKU
  obtain ⟨v, hv⟩ := hf.2 V hVc hVU
  have hgrad := energyGradient_eq_of_local_weak_derivative U V (subset_closure.trans hVU)
    X hX v hv i hg
  change ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) =ᵐ[
    volume.restrict (V : Set (Fin N → ℝ))] g at hgrad
  have hp : MemLp ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((v : GradientSpace (N := N) ⊤ q).snd i)
  exact (hp.restrict K).ae_eq (ae_restrict_of_ae_restrict_of_subset hKV hgrad)

end HeatKernel
