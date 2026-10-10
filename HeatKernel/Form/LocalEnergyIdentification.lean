-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalWeakCutoffs
public import HeatKernel.Form.LocalEnergy
import Mathlib.Tactic.Linter

/-! # Identification of local weak Sobolev and horizontal form domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein

namespace HeatKernel

/-- Local first-order weak Sobolev membership gives local representatives in the closed
horizontal graph. Measurability is stated on the ambient open set. -/
theorem memLocalEnergy_of_memSobolevXLoc {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict (U : Set (Fin N → ℝ))))
    (hf : memSobolevXLoc noDriftWeight X U 1 2 f) : MemLocalEnergy U X f := by
  refine ⟨hm, fun V hVc hVU => ?_⟩
  obtain ⟨χ, P, hP, hVP, _, hχone⟩ :=
    S.exists_test_plateau U ⟨closure (V : Set (Fin N → ℝ)), hVc⟩ hVU
  obtain ⟨W, hχW, hWc, hWU⟩ := exists_precompact_open_of_isCompact U
    χ.hasCompactSupport χ.tsupport_subset
  obtain ⟨hfp, g, hg⟩ := exists_horizontal_derivatives_of_memSobolevXLoc hf hWc hWU
  obtain ⟨z, hzf, _⟩ := exists_energyGraph_mul_of_local_weakGradient W X hX f g
    hfp (fun i => (hg i).2) (fun i => (hg i).1) χ.contDiff χ.hasCompactSupport hχW
  have hzV : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      (fun x => f x * χ x) := ae_restrict_of_ae hzf
  refine ⟨z, hzV.trans ?_⟩
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  have hone : χ x = 1 := hχone (hVP (subset_closure hx))
  rw [hone, mul_one]



end HeatKernel
