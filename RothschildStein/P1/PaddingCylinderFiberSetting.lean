-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestContinuity
public import RothschildStein.P1.PaddingFiberIntegralSmoothness
public import RothschildStein.P2.SmoothingCylinder

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- Projection of the joined-coordinate cylinder. -/
theorem padding_cylinder_subset_base {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ)) :
    (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) ⊆
      basePoint ⁻¹' (Ω : Set (Fin n → ℝ)) := by
  intro ξ hξ
  exact (P2.mem_cylinder.mp hξ).1

/-- Every product cylinder with finite fiber volume has the
actual smooth fiber setting required by the distributional descent API.
Smoothness follows from compact test support, without an extra premise. -/
theorem fiberSetting_padding_cylinder {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) ≠ ⊤) :
    P2.FiberSetting (P2.cylinder Ω J) Ω := by
  refine ⟨fun _ h => h.1, ?_, ?_⟩
  · refine ⟨(volume (J : Set (Fin d → ℝ))).toReal, ENNReal.toReal_nonneg, ?_⟩
    intro x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · rw [P2.fiberVolume_cylinder_of_mem hx, ENNReal.ofReal_toReal hJ]
    · rw [P2.fiberVolume_cylinder_of_notMem hx]
      exact bot_le
  · intro φ
    exact contDiff_joinPoint_fiberIntegral φ.contDiff φ.hasCompactSupport

/-- The existing descent fiber test is exactly the proved LF
fiber-integration map on the joined-coordinate carrier. -/
theorem paddingFiberTestCLM_eq_fiberSetting_test {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (S : P2.FiberSetting (P2.cylinder Ω J) Ω)
    (φ : _root_.TestFunction (P2.cylinder Ω J) ℝ ⊤) :
    paddingFiberTestCLM Ω (P2.cylinder Ω J) (padding_cylinder_subset_base Ω J) φ = S.test φ := by
  ext x
  rw [paddingFiberTestCLM_apply, P2.FiberSetting.test_apply]

end RothschildStein.P1
