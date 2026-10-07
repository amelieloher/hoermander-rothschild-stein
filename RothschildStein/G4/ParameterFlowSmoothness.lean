-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ParameterJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The parameterized flow is jointly smooth on stationary coordinates
(BB Lemma 9.48, pp. 441–442). -/
theorem parameterFlow_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {A : Set P} {Ω : Set E} {U : Set (P × E)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 0 < τ) (Φ : (P × E) × ℝ → E)
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v)) (Z (p.1, Φ (p, t))) t ∧ Φ (p, t) ∈ Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ) := by
  let Ψ : (P × E) × ℝ → P × E := fun q => (q.1.1, Φ q)
  let F : P × E → P × E := fun q => (0, Z q)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ Ω) := contDiffOn_const.prodMk hZ
  have hΨc : ContinuousOn Ψ (U ×ˢ Ioo (-τ) τ) := (continuousOn_fst.fst).prodMk hc
  have hinit : ∀ q ∈ U, Ψ (q, 0) = q := fun q hq => Prod.ext rfl (hΦ q hq).1
  have hsol : ∀ q ∈ U, ∀ v ∈ Ioo (-τ) τ,
      Ψ (q, v) ∈ A ×ˢ Ω ∧ HasDerivAt (fun w => Ψ (q, w)) (F (Ψ (q, v))) v := by
    intro q hq v hv
    exact ⟨⟨(hUA hq).1, ((hΦ q hq).2 v hv).2⟩,
      (hasDerivAt_const v q.1).prodMk ((hΦ q hq).2 v hv).1⟩
  have hjoint := (RothschildStein.G1.local_flow_contDiffOn
    (hA.prod hΩ) hU hτ hF hΨc hinit hsol).snd
  exact hjoint

end RothschildStein.G4
