-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialPowerJets
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Repeated field derivatives depend only on the local smooth
representative; eventual equality suffices for every finite power. -/
theorem fieldPower_eventuallyEq {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (n : ℕ) {x : Fin N → ℝ}
    {f g : (Fin N → ℝ) → ℝ} (he : f =ᶠ[𝓝 x] g) :
    fieldPower V n f =ᶠ[𝓝 x] fieldPower V n g := by
  induction n generalizing f g with
  | zero => exact he
  | succ n ih =>
    apply ih
    filter_upwards [he.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun D => D (V y)) hy

/-- Mixed powers of bundled operators are exactly the ordered
actual field powers of the two-flow pullback Taylor formula. -/
theorem smoothFieldOperator_mixed_pow_apply {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (m n : ℕ) (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (((smoothFieldOperator Ω U hU) ^ m * (smoothFieldOperator Ω V hV) ^ n) f).val x =
      fieldPower U m (fieldPower V n f.val) x := by
  rw [Module.End.mul_apply, smoothFieldOperator_pow_apply Ω U hU m _ hx]
  have he : (((smoothFieldOperator Ω V hV) ^ n) f).val =ᶠ[𝓝 x]
      fieldPower V n f.val := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact smoothFieldOperator_pow_apply Ω V hV n f hy
  exact (fieldPower_eventuallyEq U m he).eq_of_nhds
end RothschildStein.G3
