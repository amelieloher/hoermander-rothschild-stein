-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalEnergy
import Mathlib.Tactic.Linter

/-! # Addition and smooth functions in local horizontal energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Local energy membership depends only on the almost everywhere class. -/
theorem MemLocalEnergy.congr_ae {f g : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (he : f =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] g) :
    MemLocalEnergy U X g := by
  refine ⟨hf.1.congr he, fun V hc hs => ?_⟩
  obtain ⟨w, hw⟩ := hf.2 V hc hs
  exact ⟨w, hw.trans (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hs) he)⟩

/-- Local energy functions are closed under addition. -/
theorem MemLocalEnergy.add {f g : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) (hg : MemLocalEnergy U X g) : MemLocalEnergy U X (f + g) := by
  refine ⟨hf.1.add hg.1, fun V hc hs => ?_⟩
  obtain ⟨v, hv⟩ := hf.2 V hc hs
  obtain ⟨w, hw⟩ := hg.2 V hc hs
  refine ⟨v + w, ?_⟩
  have H : ((v + w : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => (v : GradientSpace (N := N) ⊤ q).fst x + (w : GradientSpace (N := N) ⊤ q).fst x) := by
    simpa only [Submodule.coe_add, WithLp.add_fst, Pi.add_def, Opens.coe_top, Measure.restrict_univ]
      using Lp.coeFn_add (v : GradientSpace (N := N) ⊤ q).fst (w : GradientSpace (N := N) ⊤ q).fst
  have HV : ((v + w : energyGraph (N := N) ⊤ X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      (fun x => (v : GradientSpace (N := N) ⊤ q).fst x + (w : GradientSpace (N := N) ⊤ q).fst x) := ae_restrict_of_ae H
  filter_upwards [HV, hv, hw] with x hx hvx hwx
  simp only [Pi.add_apply]
  rw [hx, hvx, hwx]

/-- Smooth functions belong to every local horizontal energy domain. -/
theorem memLocalEnergy_of_contDiff (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : MemLocalEnergy U X f := by
  refine ⟨hf.continuous.aestronglyMeasurable, fun V hc hs => ?_⟩
  obtain ⟨χ, P, _, hKP, _, hχ⟩ := S.exists_test_plateau U ⟨closure (V : Set (Fin N → ℝ)), hc⟩ hs
  obtain ⟨w, hw, hwf⟩ := exists_smoothGradientPair X
    (hf.mul χ.contDiff) (χ.hasCompactSupport.mul_left (f := f)) hX
  refine ⟨⟨w, smoothGradientSpan_le_energyGraph ⊤ X (Submodule.subset_span hw)⟩, ?_⟩
  have H : w.fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] (fun x => f x * χ x) :=
    ae_restrict_of_ae hwf
  refine H.trans ?_
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  rw [hχ (hKP (subset_closure hx))]
  simp only [Pi.one_apply, mul_one]


end HeatKernel
