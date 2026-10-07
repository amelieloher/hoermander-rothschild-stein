-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.UniformBufferedFlow
public import RothschildStein.G1.MixedJetTimeScale

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

/-- The smaller mixed-jet time cylinder is selected from numerical
clearance and coefficient bounds before the field and starting set. The
actual smooth flow exists uniformly near that set and has full mixed time
and initial-point jets controlled by finite field jets alone
(BB Prop 1.2, pp. 3–4). -/
theorem exists_uniform_buffered_finiteJet_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [ProperSpace E]
    (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B) (r : ℕ) :
    let τ : ℝ := 2 * (R / (16 * (1 + B)))
    ∃ ε : ℝ, 0 < ε ∧ 4 * ε < τ ∧
      ∀ {Ω K : Set E}, IsOpen Ω → ∀ (Z : E → E),
        ContDiffOn ℝ (⊤ : ℕ∞) Z Ω →
        (∀ x ∈ K, closedBall x R ⊆ Ω) →
        (∀ x ∈ Ω, ∀ j ≤ r, ‖iteratedFDeriv ℝ j Z x‖ ≤ B) →
        ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
          ∃ Φ : E × ℝ → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ) ∧
            (∀ x ∈ U, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
              Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t) ∧
            ∀ x ∈ U, ∀ t, |t| < ε → ‖Φ (x, t) - x‖ ≤ B * |t| ∧
              ∀ n, 1 ≤ n → n ≤ r →
                ‖iteratedFDeriv ℝ n (fun q : ℝ × E => Φ (q.2, q.1)) (t, x)‖ ≤
                  2 * (1 + ε⁻¹) ^ n := by
  intro τ
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨ε, hε, hετ, hsmall⟩ := exists_mixedJet_time_scale hτ hB r
  refine ⟨ε, hε, hετ, ?_⟩
  intro Ω K hΩ Z hZ hRΩ hjet
  have hvalue : ∀ x ∈ Ω, ‖Z x‖ ≤ B := fun x hx => by
    simpa only [norm_iteratedFDeriv_zero] using hjet x hx 0 (Nat.zero_le r)
  obtain ⟨U, hU, hKU, hUΩ, Φ, hs, hsol⟩ :=
    exists_uniform_buffered_smooth_flow hΩ hZ hR hB hRΩ hvalue
  refine ⟨U, hU, hKU, hUΩ, Φ, hs, hsol, ?_⟩
  have hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t ∧ Φ (x, t) ∈ Ω :=
    fun x hx => ⟨(hsol x hx).1, fun t ht => ⟨((hsol x hx).2 t ht).2, ((hsol x hx).2 t ht).1⟩⟩
  intro x hx t ht
  have htτ : t ∈ Ioo (-τ) τ := abs_lt.mp (ht.trans (by linarith))
  refine ⟨?_, localFlow_mixedJets_le hΩ hU hUΩ hZ hε hετ Φ hs.continuousOn hΦ
    r hB hjet hsmall hx ht⟩
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset hzero htτ
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => ((hΦ x hx).2 v (hsub hv)).1.hasDerivWithinAt)
    (fun v hv => hvalue _ ((hΦ x hx).2 v (hsub hv)).2)
    (convex_uIcc (0 : ℝ) t) left_mem_uIcc right_mem_uIcc
  simpa only [(hΦ x hx).1, sub_zero, Real.norm_eq_abs] using hh

end RothschildStein.G1
