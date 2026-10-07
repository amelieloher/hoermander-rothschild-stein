-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingIntrinsic

/-!
# Distributional smoothing, descent: chart-free forms

With the continuity and smoothness of the fiber integral proved (`SmoothingFiberCLM`), every cylinder
`A × B` with `|B| < ∞` carries a fiber integration `J : D(A × B) → D(A)` and a lift `T̃ = T ∘ J`
of distributions on `A`, without a lifted chart. The descent step of the distributional smoothing theorem is then stated for
this lift: if `T̃` is represented by `w`, then `T` is represented by the vertical average of `w` and
`w` is its lift (`FiberIntegration.descent`); lifted word derivatives descend
(`FiberIntegration.hasWeakWordDeriv_descent`). This is the "cylinder argument" invoked by the
low-dimension reduction of the local regularity theorem (product padding of the original equation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2
variable {n m : ℕ}

section Chart

variable {k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

end Chart

section Restriction

variable {N : ℕ}

/-- Restriction is transitive: restricting to `U''` and then to `U'` is restricting to `U'`. -/
theorem distributionRestriction_restriction (U U'' U' : Opens (Fin N → ℝ)) (h1 : U' ≤ U'')
    (h2 : U'' ≤ U) (T : Distribution U ℝ (⊤ : ℕ∞)) :
    RothschildStein.S.distributionRestrictionCLM U'' U'
        (RothschildStein.S.distributionRestrictionCLM U U'' T) =
      RothschildStein.S.distributionRestrictionCLM U U' T := by
  ext ψ
  rw [RothschildStein.S.distributionRestrictionCLM_apply U'' U' h1,
    RothschildStein.S.distributionRestrictionCLM_apply U U'' h2,
    RothschildStein.S.distributionRestrictionCLM_apply U U' (h1.trans h2)]
  rfl

/-- The restriction of a regular distribution is the regular distribution of the same function. -/
theorem distributionRestriction_ofFun (U U' : Opens (Fin N → ℝ)) (hU : U' ≤ U)
    {f : (Fin N → ℝ) → ℝ} (hf : LocallyIntegrableOn f (U : Set (Fin N → ℝ)) volume) :
    RothschildStein.S.distributionRestrictionCLM U U' (Distribution.ofFun U f volume (⊤ : ℕ∞)) =
      Distribution.ofFun U' f volume (⊤ : ℕ∞) := by
  ext ψ
  rw [RothschildStein.S.distributionRestrictionCLM_apply U U' hU, Distribution.ofFun_apply hf,
    Distribution.ofFun_apply (hf.mono_set hU)]
  rfl

end Restriction

end RothschildStein.P2
