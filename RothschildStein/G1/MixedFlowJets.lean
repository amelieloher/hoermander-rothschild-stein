-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.TimeRescaledFlows

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Actual mixed time/initial-point derivatives on a smaller
cylinder have a uniform finite coefficient-jet bound. The order-zero
position of the compact starting set does not enter (BB pp. 3–4). -/
theorem localFlow_mixedJets_le {E : Type*}
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
    {x : E} (hx : x ∈ U) {t : ℝ} (ht : |t| < ε) :
    ∀ n, 1 ≤ n → n ≤ r →
      ‖iteratedFDeriv ℝ n (fun q : ℝ × E => Φ (q.2, q.1)) (t, x)‖ ≤
        2 * (1 + ε⁻¹) ^ n := by
  let S : Set (ℝ × E) := Ioo (-2) 2 ×ˢ U
  let g : ℝ × E → E := fun q => Φ (q.2, ε * q.1)
  let L : (ℝ × E) →L[ℝ] (ℝ × E) :=
    (ε⁻¹ • ContinuousLinearMap.fst ℝ ℝ E).prod (ContinuousLinearMap.snd ℝ ℝ E)
  have hτ : 0 < τ := by linarith
  have hΦsmooth := local_flow_contDiffOn hΩ hU hτ hZ hc
    (fun y hy => (hΦ y hy).1)
    (fun y hy v hv => ⟨((hΦ y hy).2 v hv).2, ((hΦ y hy).2 v hv).1⟩)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g S :=
    hΦsmooth.comp (by fun_prop) (by
      intro q hq
      refine ⟨hq.2, ?_⟩
      have ha : |q.1| < 2 := abs_lt.mpr hq.1
      have hh : |ε * q.1| < τ := by
        rw [abs_mul, abs_of_pos hε]
        nlinarith [mul_lt_mul_of_pos_left ha hε]
      exact abs_lt.mp hh)
  have ha : |ε⁻¹ * t| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    exact (inv_mul_lt_one₀ hε).mpr ht |>.le
  have hp : L (t, x) ∈ S := ⟨abs_lt.mp (ha.trans_lt (by norm_num)), hx⟩
  have hL : ‖L‖ ≤ 1 + ε⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
    intro q
    change ‖(ε⁻¹ * q.1, q.2)‖ ≤ (1 + ε⁻¹) * ‖q‖
    rw [Prod.norm_def, max_le_iff]
    constructor
    · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
      calc
        _ ≤ ε⁻¹ * ‖q‖ := mul_le_mul_of_nonneg_left (norm_fst_le q) (inv_nonneg.mpr hε.le)
        _ ≤ _ := by nlinarith [norm_nonneg q]
    · calc
        ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
        _ ≤ _ := by nlinarith [mul_nonneg (inv_nonneg.mpr hε.le) (norm_nonneg q)]
  intro n hn hnr
  have hj := localFlow_time_rescaled_jets_lt_two hΩ hU hUΩ hZ hε hετ Φ hc hΦ
    r hB hbound hsmall hx ha n hn hnr
  have hj' : ‖iteratedFDeriv ℝ n g (L (t, x))‖ ≤ 2 := hj.le
  have hh := norm_local_linear_reparametrized_jet_le (isOpen_Ioo.prod hU) hg L hp n
    (by norm_num : (0 : ℝ) ≤ 2) hj' hL
  have heq : g ∘ L = (fun q : ℝ × E => Φ (q.2, q.1)) := by
    funext q
    simp [g, L, hε.ne']
  rw [heq] at hh
  exact hh

end RothschildStein.G1
