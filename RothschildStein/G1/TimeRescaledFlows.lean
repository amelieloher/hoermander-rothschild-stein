-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.TimeRescaledFieldJets
public import RothschildStein.G1.LinearReparametrizedJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G1

/-- Mixed time and initial-point jets are parameter jets of an
actual flow with an additional constant speed parameter (BB pp. 3–4).
The normalized time cylinder uses only finitely many coefficient jets. -/
theorem localFlow_time_rescaled_jets_lt_two {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    {Z : E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω)
    {τ ε B : ℝ} (hε : 0 < ε) (hετ : 4 * ε < τ)
    (Φ : E × ℝ → E) (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t ∧ Φ (x, t) ∈ Ω)
    (r : ℕ) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ Ω, ∀ j ≤ r, ‖iteratedFDeriv ℝ j Z x‖ ≤ B)
    (hsmall : spatialJetRate r (ε * 2 ^ r * r.factorial * B) < 1)
    {x : E} (hx : x ∈ U) {a : ℝ} (ha : |a| ≤ 1) :
    ∀ n, 1 ≤ n → n ≤ r →
      ‖iteratedFDeriv ℝ n (fun q : ℝ × E => Φ (q.2, ε * q.1)) (a, x)‖ < 2 := by
  let A : Set ℝ := Ioo (-2) 2
  let V : Set (ℝ × E) := A ×ˢ U
  let H : ℝ × E → E := fun q => (ε * q.1) • Z q.2
  let Ψ : (ℝ × E) × ℝ → E := fun q => Φ (q.1.2, ε * q.1.1 * q.2)
  have htime : ∀ c ∈ A, ∀ v ∈ Ioo (-2 : ℝ) 2, ε * c * v ∈ Ioo (-τ) τ := by
    intro c hc v hv
    have hac : |c| ≤ 2 := (abs_lt.mpr hc).le
    have hav : |v| ≤ 2 := (abs_lt.mpr hv).le
    have hm : |c| * |v| ≤ 4 := by nlinarith [mul_le_mul_of_nonneg_right hac (abs_nonneg v)]
    have hh : |ε * c * v| < τ := by
      rw [abs_mul, abs_mul, abs_of_pos hε]
      nlinarith [mul_le_mul_of_nonneg_left hm hε.le]
    exact abs_lt.mp hh
  have hΨc : ContinuousOn Ψ (V ×ˢ Ioo (-2 : ℝ) 2) :=
    hc.comp (by fun_prop)
      (fun q hq => ⟨hq.1.2, htime q.1.1 hq.1.1 q.2 hq.2⟩)
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H (A ×ˢ Ω) :=
    (contDiffOn_const.mul contDiffOn_fst).smul
      (hZ.comp contDiffOn_snd (fun q hq => hq.2))
  have hΨ : ∀ q ∈ V, Ψ (q, 0) = q.2 ∧ ∀ v ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun w => Ψ (q, w)) (H (q.1, Ψ (q, v))) v ∧ Ψ (q, v) ∈ Ω := by
    intro q hq
    refine ⟨by simpa [Ψ] using (hΦ q.2 hq.2).1, ?_⟩
    intro v hv
    have hs := (hΦ q.2 hq.2).2 (ε * q.1 * v) (htime q.1 hq.1 v hv)
    refine ⟨?_, hs.2⟩
    simpa [Ψ, H, mul_assoc, Function.comp_def] using hs.1.scomp v ((hasDerivAt_id v).const_mul (ε * q.1))
  have hp : (a, x) ∈ V := ⟨abs_lt.mp (ha.trans_lt (by norm_num)), hx⟩
  have hh := parameterFlow_spatialJets_bound isOpen_Ioo hΩ (isOpen_Ioo.prod hU)
    (fun q hq => ⟨hq.1, hUΩ hq.2⟩) hH (by norm_num : (0 : ℝ) < 2)
    Ψ hΨc hΨ r hp (by norm_num : (1 : ℝ) ∈ Ioo (-2) 2)
    (by positivity : 0 ≤ ε * 2 ^ r * r.factorial * B)
    (fun v hv j hj => by
      have hvr : v ∈ Ioo (-2 : ℝ) 2 := by
        rw [uIcc_of_le zero_le_one] at hv
        constructor <;> linarith [hv.1, hv.2]
      have hpt := (hΨ (a, x) hp).2 v hvr
      apply (norm_time_rescaled_field_jet_le hΩ hZ hpt.2 ha hε.le hB r
        (hbound _ hpt.2) j hj).trans
      gcongr
      norm_num)
    (by simpa using hsmall)
  simpa only [Ψ, mul_one] using hh

end RothschildStein.G1
