-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalLipschitzCalculus
public import HeatKernel.Form.LocalEnergyAlgebra
import Mathlib.Tactic.Linter

/-! # Lipschitz scalar composition on local horizontal energy domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Every Lipschitz scalar map preserves the local energy domain, with any value at zero. -/
theorem MemLocalEnergy.comp_lipschitz_scalar {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLocalEnergy U X f) {η : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C η) :
    MemLocalEnergy U X (η ∘ f) := by
  let ψ : ℝ → ℝ := fun s => η s - η 0
  have hψ : LipschitzWith C ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ, dist_sub_right] using hLip.dist_le_mul x y
  have hzero : ψ 0 = 0 := sub_self _
  have H := (hf.comp_lipschitz U X hX hψ hzero).add U X
    (memLocalEnergy_of_contDiff U X hX (contDiff_const (c := η 0)))
  apply H.congr_ae U X
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, Function.comp_apply, ψ, sub_add_cancel]



end HeatKernel
