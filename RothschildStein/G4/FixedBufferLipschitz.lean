-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalFieldBuffer

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped NNReal

namespace RothschildStein.G4

/-- A smooth field is Lipschitz on any prescribed compact ball
inside its open domain. This auxiliary Lipschitz constant need not enter
the numerical time-one radius, which only uses a field-value bound. -/
theorem exists_lipschitzOnWith_on_fixed_buffer {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {Ω : Set E} (hΩ : IsOpen Ω)
    {Z : E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    (x₀ : E) (R : ℝ) (hRΩ : closedBall x₀ R ⊆ Ω) :
    ∃ K : ℝ≥0, LipschitzOnWith K Z (closedBall x₀ R) := by
  have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ Z) Ω :=
    hZ.fderiv_of_isOpen hΩ (by simp)
  have hd : ContinuousOn (fderiv ℝ Z) Ω := hdf.continuousOn
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ R).image_of_continuousOn
    (hd.mono hRΩ)).isBounded.exists_norm_le
  let P := |C| + 1
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨Real.toNNReal P, ?_⟩
  apply (convex_closedBall x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro x hx
    exact ((hZ.contDiffAt (hΩ.mem_nhds (hRΩ hx))).differentiableAt (by simp))
  · intro x hx
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hP.le]
    change ‖fderiv ℝ Z x‖ ≤ P
    exact ((hC _ (mem_image_of_mem _ hx)).trans (le_abs_self C)).trans (by dsimp [P]; linarith)

end RothschildStein.G4
