-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.QuantitativeTimeFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

/-- A prescribed buffer and field-value bound give a smooth
actual local flow on an explicit time interval. Auxiliary Lipschitz
constants do not enter the numerical radius (BB Prop 1.2, pp. 3–4). -/
theorem exists_smooth_buffered_local_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [ProperSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (x₀ : E) {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hRΩ : closedBall x₀ R ⊆ Ω)
    (hbound : ∀ x ∈ closedBall x₀ R, ‖Z x‖ ≤ B) :
    let κ : ℝ := R / (16 * (1 + B))
    ∃ Φ : E × ℝ → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ
      (ball x₀ (R / 4) ×ˢ Ioo (-(2 * κ)) (2 * κ)) ∧
      ∀ x ∈ ball x₀ (R / 4), Φ (x, 0) = x ∧
        ∀ t ∈ Ioo (-(2 * κ)) (2 * κ), Φ (x, t) ∈ closedBall x₀ R ∧
          HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  intro κ
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let F : E → E := fun x => κ • Z x
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F Ω := hZ.const_smul κ
  have hFb : ∀ x ∈ closedBall x₀ R, ‖F x‖ ≤ R / 16 := by
    intro x hx
    change ‖κ • Z x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    apply (mul_le_mul_of_nonneg_left (hbound x hx) hκ.le).trans
    dsimp [κ]
    have hd : 0 < 16 * (1 + B) := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith
  obtain ⟨Ψ, hΨ, hsol⟩ := RothschildStein.G4.exists_smooth_fixed_time_flow
    hΩ hF x₀ hR hRΩ hFb
  let T : E × ℝ → E × ℝ := fun q => (q.1, q.2 / κ)
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by dsimp [T]; fun_prop
  have htime : ∀ t ∈ Ioo (-(2 * κ)) (2 * κ), t / κ ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht
    exact ⟨(lt_div_iff₀ hκ).mpr (by linarith [ht.1]), (div_lt_iff₀ hκ).mpr ht.2⟩
  refine ⟨fun q => Ψ (T q), hΨ.comp hT.contDiffOn
    (fun q hq => ⟨hq.1, htime q.2 hq.2⟩), ?_⟩
  intro x hx
  refine ⟨by simpa only [T, zero_div] using (hsol x hx).1, ?_⟩
  intro t ht
  have hs := (hsol x hx).2 (t / κ) (htime t ht)
  refine ⟨hs.1, ?_⟩
  have hh := hs.2.scomp t ((hasDerivAt_id t).div_const κ)
  simpa only [T, F, Function.comp_def, id_eq, one_div, smul_smul,
    inv_mul_cancel₀ hκ.ne', one_smul] using hh

end RothschildStein.G1
