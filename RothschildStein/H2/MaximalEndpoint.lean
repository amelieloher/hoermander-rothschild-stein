-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.MaximalWeak
public import RothschildStein.H2.Patches
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The bundled patch provides precisely the weak-type
hypothesis of the differentiation theorem. -/
theorem DoublingPatch.maximal_weak_type (P : DoublingPatch X) :
    PatchMaximalWeakType P.μ P.S P.W P.ρ P.C_D :=
  patchMaximal_weak_type P.μ P.S P.W P.ρ P.C_D P.ρ_pos P.one_lt_C_D
    P.incl P.doubling ⟨P.measurable_W, P.finite_W⟩

/-- Unconditional differentiation on the bundled doubling patch
(BB Theorem 7.27, pp. 314–316). -/
theorem DoublingPatch.lebesgue_differentiation (P : DoublingPatch X)
    (f : X → ℝ) (hf : IntegrableOn f P.W P.μ) :
    ∀ᵐ x ∂P.μ, x ∈ P.S →
      Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x| ∂P.μ) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r : ℝ => ⨍ y in ball x r, f y ∂P.μ) (𝓝[>] 0) (𝓝 (f x)) ∧
      ‖f x‖ₑ ≤ patchMaximal P.μ P.S P.ρ f x :=
  lebesgue_differentiation_of_patch_hypotheses P.μ P.S P.W P.ρ P.C_D P.ρ_pos
    P.one_lt_C_D P.incl P.doubling ⟨P.measurable_W, P.finite_W⟩ f hf

end RothschildStein.H2
