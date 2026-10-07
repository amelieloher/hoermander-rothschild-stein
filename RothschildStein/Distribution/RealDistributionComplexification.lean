-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.RealRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- complexify the values of a real
actual distribution; its test carrier remains real. -/
def realDistributionToComplex {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) : Distribution Ω ℂ (⊤ : ℕ∞) :=
  Complex.ofRealCLM.postcompCompactConvergenceCLM (TestFunction Ω ℝ (⊤ : ℕ∞)) T

/-- scalar conversion preserves every
real compact-test pairing exactly. -/
theorem realDistributionToComplex_apply {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    realDistributionToComplex Ω T ψ = (T ψ : ℂ) := rfl

/-- converting a function distribution
agrees with converting its function, with the same volume measure. -/
theorem realDistributionToComplex_ofFun {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (g : (Fin N → ℝ) → ℝ) (hg : LocallyIntegrableOn g (Ω : Set (Fin N → ℝ)) volume) :
    realDistributionToComplex Ω (Distribution.ofFun Ω g volume (⊤ : ℕ∞)) =
      Distribution.ofFun Ω (fun x => (g x : ℂ)) volume (⊤ : ℕ∞) := by
  have hgc : LocallyIntegrableOn (fun x => (g x : ℂ)) (Ω : Set (Fin N → ℝ)) volume :=
    Complex.ofRealCLM.locallyIntegrableOn_comp hg
  ext ψ
  rw [realDistributionToComplex_apply, Distribution.ofFun_apply hg, Distribution.ofFun_apply hgc]
  have he := Complex.ofRealCLM.integral_comp_comm (ψ.integrable_smul hg)
  simpa using he.symm

end RothschildStein.Distribution
