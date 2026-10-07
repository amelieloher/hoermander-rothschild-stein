-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluationSmoothness
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1
open G3

/-- Freeness persists near a free point
(BB Proposition 10.13, pp. 488–489). -/
theorem freeAt_eventually_unrestricted {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hfree : FreeAt p s X x) :
    ∀ᶠ y in 𝓝 x, y ∈ Ω ∧ FreeAt p s X y := by
  let b := Module.finBasis ℝ (formalSpan a s p)
  have hi := (freeAt_iff_directPointEvaluation_injective Ω X hX hx).mp hfree
  have hb := (directPointEvaluation_injective_iff_basis_independent Ω X hX x b).mp hi
  have hc : ContinuousAt (fun y => fun j => directPointEvaluation (s := s) (p := p) Ω X hX y (b j)) x := by
    apply continuousAt_pi.mpr
    intro j
    exact (directPointEvaluation_contDiffOn Ω X hX (b j)).continuousOn.continuousAt
      (Ω.isOpen.mem_nhds hx)
  have he := hc.tendsto.eventually hb.eventually
  filter_upwards [Ω.isOpen.mem_nhds hx,he] with y hy hby
  exact ⟨hy,(freeAt_iff_directPointEvaluation_injective Ω X hX hy).mpr
    ((directPointEvaluation_injective_iff_basis_independent Ω X hX y b).mpr hby)⟩
end RothschildStein.L1
