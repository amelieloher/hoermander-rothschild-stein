-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.LocalFlows
public import RothschildStein.S.Transposes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
@[expose] public section
noncomputable section
open Set Filter
open TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Repeated differentiation along one field, in pullback order
(BB (9.9), pp. 410–411). -/
def fieldPower {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ)) :
    ℕ → ((Fin N → ℝ) → ℝ) → ((Fin N → ℝ) → ℝ)
  | 0, f => f
  | n + 1, f => fieldPower V n (fieldDerivative V f)

/-- Every fixed field power preserves smoothness on its open domain
(BB (9.9), pp. 410–411). -/
theorem contDiffOn_fieldPower {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω) (n : ℕ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fieldPower V n f) Ω := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ (S.contDiffOn_fieldDerivative Ω V f hV hf)

/-- Actual smooth integral curves have exactly the formal exponential
pullback jets, at every time in their open interval (BB (9.9), pp. 410–411). -/
theorem iteratedDeriv_pullback_integralCurve {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    {J : Set ℝ} (hJ : IsOpen J) (α : ℝ → (Fin N → ℝ))
    (hODE : ∀ t ∈ J, HasDerivAt α (V (α t)) t)
    (hmem : ∀ t ∈ J, α t ∈ Ω) (n : ℕ)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {t : ℝ} (ht : t ∈ J) :
    iteratedDeriv n (fun r => f (α r)) t = fieldPower V n f (α t) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun r => f (α r)) =ᶠ[𝓝 t]
        (fun r => fieldDerivative V f (α r)) := by
      filter_upwards [hJ.mem_nhds ht] with r hr
      exact (G1.integralCurve_chain_rule (hODE r hr)
        ((hf.contDiffAt (Ω.isOpen.mem_nhds (hmem r hr))).differentiableAt (by simp))).deriv
    rw [he.iteratedDeriv_eq n]
    exact ih _ (S.contDiffOn_fieldDerivative Ω V f hV hf)
end RothschildStein.G3
