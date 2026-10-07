-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ParameterJetBounds
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G1

/-- Joint parameter and initial-point jets of an actual continuous
parameter flow have the explicit finite coefficient-jet bound, using the
proved smooth-dependence theorem on stationary parameter coordinates
(BB Prop 1.2, pp. 3–4). -/
theorem parameterFlow_spatialJets_bound {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {A : Set P} {Ω : Set E} {U : Set (P × E)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 0 < τ) (Φ : (P × E) × ℝ → E)
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (r : ℕ) {p : P × E} (hp : p ∈ U) {t B : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hB : 0 ≤ B)
    (hbound : ∀ v ∈ uIcc 0 t, ∀ j ≤ r,
      ‖iteratedFDeriv ℝ j Z (p.1, Φ (p, v))‖ ≤ B)
    (hsmall : spatialJetRate r B * |t| < 1) :
    ∀ n, 1 ≤ n → n ≤ r → ‖iteratedFDeriv ℝ n (fun q => Φ (q, t)) p‖ < 2 := by
  let Ψ : (P × E) × ℝ → P × E := fun q => (q.1.1, Φ q)
  let F : P × E → P × E := fun q => (0, Z q)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ Ω) := contDiffOn_const.prodMk hZ
  have hΨc : ContinuousOn Ψ (U ×ˢ Ioo (-τ) τ) :=
    (continuousOn_fst.fst).prodMk hc
  have hinit : ∀ q ∈ U, Ψ (q, 0) = q := fun q hq => Prod.ext rfl (hΦ q hq).1
  have hsol : ∀ q ∈ U, ∀ v ∈ Ioo (-τ) τ,
      Ψ (q, v) ∈ A ×ˢ Ω ∧ HasDerivAt (fun w => Ψ (q, w)) (F (Ψ (q, v))) v := by
    intro q hq v hv
    exact ⟨⟨(hUA hq).1, ((hΦ q hq).2 v hv).2⟩,
      (hasDerivAt_const v q.1).prodMk ((hΦ q hq).2 v hv).1⟩
  have hjoint := (local_flow_contDiffOn (hA.prod hΩ) hU hτ hF hΨc hinit hsol).snd
  exact parameterFlow_spatialJets_bound_of_joint_contDiff hA hΩ hU hUA hZ hτ
    Φ hjoint hΦ r hp ht hB hbound hsmall

end RothschildStein.G1
