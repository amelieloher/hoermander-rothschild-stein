-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFields
public import RothschildStein.G4.TimeOneFlow
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

theorem shortFlow_rescaled_timeOne_contDiffOn {m N : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))} {τ ε : ℝ}
    (hε : 0 < ε) (hετ : 4*ε < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Φ ∘ G4.flowScale (ε/4))
      (({q : (Fin m → ℝ) × (Fin N → ℝ) | ((ε/4)⁻¹ • q.1,q.2) ∈ U}) ×ˢ Ioo (-2) 2) := by
  apply hΦ.comp (G4.flowScale_contDiff (ε/4)).contDiffOn
  intro q hq
  refine ⟨hq.1,?_⟩
  change (ε/4)*q.2 ∈ Ioo (-τ) τ
  have ht : |q.2| < 2 := abs_lt.mpr hq.2
  have htime : |(ε/4)*q.2| < τ := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < ε/4)]
    have hm := mul_lt_mul_of_pos_left ht (by positivity : 0 < ε/4)
    nlinarith
  exact abs_lt.mp htime

theorem shortFlow_rescaled_timeOne_ode {m N : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))} {Ω : Set (Fin N → ℝ)} {τ ε : ℝ}
    (hε : 0 < ε) (hετ : 4*ε < τ)
    (Y : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hODE : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      Φ (q,t) ∈ Ω ∧ HasDerivAt (fun v => Φ (q,v))
        (∑ j, q.1 j • Y j (Φ (q,t))) t) :
    ∀ q : (Fin m → ℝ) × (Fin N → ℝ), ((ε/4)⁻¹ • q.1,q.2) ∈ U →
      (Φ ∘ G4.flowScale (ε/4)) (q,0) = q.2 ∧ ∀ t ∈ Ioo (-2 : ℝ) 2,
        (Φ ∘ G4.flowScale (ε/4)) (q,t) ∈ Ω ∧
        HasDerivAt (fun v => (Φ ∘ G4.flowScale (ε/4)) (q,v))
          (∑ j, q.1 j • Y j ((Φ ∘ G4.flowScale (ε/4)) (q,t))) t := by
  intro q hq
  have hθ : 0 < ε/4 := by positivity
  have he := hODE ((ε/4)⁻¹ • q.1,q.2) hq
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_apply,G4.flowScale,mul_zero] using he.1
  · intro t ht
    have ht' : (ε/4)*t ∈ Ioo (-τ) τ := by
      have hh : |(ε/4)*t| < τ := by
        rw [abs_mul,abs_of_pos hθ]
        have hm := mul_lt_mul_of_pos_left (abs_lt.mpr ht) hθ
        nlinarith
      exact abs_lt.mp hh
    refine ⟨(he.2 _ ht').1,?_⟩
    exact G4.rescale_constantCombination_derivative Y hθ q.1
      (fun v => Φ (((ε/4)⁻¹ • q.1,q.2),v)) (he.2 _ ht').2
end RothschildStein.G3
