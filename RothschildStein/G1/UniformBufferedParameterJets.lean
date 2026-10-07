-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.UniformBufferedFiniteJets
public import RothschildStein.G1.ParameterJets
public import RothschildStein.G1.MixedFlowDisplacement

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

/-- Uniform numerical clearance and mixed coefficient jets give
an actual jointly smooth parameter flow and all mixed time/parameter/spatial
jet bounds on one smaller cylinder, selected before the actual field.
Parameters remain stationary (BB Prop 1.2, pp. 3–4). -/
theorem exists_uniform_buffered_parameterJet_flow {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P] [ProperSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [ProperSpace E]
    (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B) (r : ℕ) :
    let τ : ℝ := 2 * (R / (16 * (1 + B)))
    ∃ ε : ℝ, 0 < ε ∧ 4 * ε < τ ∧
      ∀ {A : Set P} {Ω : Set E} {K : Set (P × E)}, IsOpen A → IsOpen Ω →
        ∀ (Z : P × E → E), ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) →
        (∀ p ∈ K, closedBall p R ⊆ A ×ˢ Ω) →
        (∀ p ∈ A ×ˢ Ω, ∀ j ≤ r, ‖iteratedFDeriv ℝ j Z p‖ ≤ B) →
        ∃ U : Set (P × E), IsOpen U ∧ K ⊆ U ∧ U ⊆ A ×ˢ Ω ∧
          ∃ Φ : ((P × E) × ℝ) → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ) ∧
            (∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ t ∈ Ioo (-τ) τ,
              Φ (p, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (p, v)) (Z (p.1, Φ (p, t))) t) ∧
            ∀ p ∈ U, ∀ t, |t| < ε → ‖Φ (p, t) - p.2‖ ≤ B * |t| ∧
              ∀ n, 1 ≤ n → n ≤ r →
                ‖iteratedFDeriv ℝ n (fun q : ℝ × (P × E) => Φ (q.2, q.1)) (t, p)‖ ≤
                  2 * (1 + ε⁻¹) ^ n ∧
                ‖iteratedFDeriv ℝ n (fun q : ℝ × (P × E) => Φ (q.2, q.1) - q.2.2) (t, p)‖ ≤
                  2 * (1 + ε⁻¹) ^ n + 1 := by
  intro τ
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨ε, hε, hετ, hpackage⟩ := exists_uniform_buffered_finiteJet_flow
    (E := P × E) R B hR hB r
  refine ⟨ε, hε, hετ, ?_⟩
  intro A Ω K hA hΩ Z hZ hRΩ hjet
  let F : P × E → P × E := fun p => (0, Z p)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ Ω) := contDiffOn_const.prodMk hZ
  have hFjet : ∀ p ∈ A ×ˢ Ω, ∀ j ≤ r, ‖iteratedFDeriv ℝ j F p‖ ≤ B := by
    intro p hp j hj
    exact (stationaryLift_jet_norm_le (hZ.contDiffAt ((hA.prod hΩ).mem_nhds hp)) j).trans
      (hjet p hp j hj)
  obtain ⟨U, hU, hKU, hUA, Ψ, hΨ, hsol, hnorm⟩ :=
    hpackage (hA.prod hΩ) F hF hRΩ hFjet
  have hstationary : ∀ p ∈ U, ∀ t ∈ Ioo (-τ) τ, (Ψ (p, t)).1 = p.1 := by
    intro p hp t ht
    have hd : ∀ v ∈ Ioo (-τ) τ, HasDerivAt (fun v => (Ψ (p, v)).1) 0 v := by
      intro v hv
      exact (ContinuousLinearMap.fst ℝ P E).hasFDerivAt.comp_hasDerivAt v ((hsol p hp).2 v hv).2
    have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
    have hh := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hd v hv).deriv) ht hzero
    exact hh.trans (congrArg Prod.fst (hsol p hp).1)
  let Φ : ((P × E) × ℝ) → E := fun q => (Ψ q).2
  refine ⟨U, hU, hKU, hUA, Φ, hΨ.snd, ?_, ?_⟩
  · intro p hp
    refine ⟨congrArg Prod.snd (hsol p hp).1, ?_⟩
    intro t ht
    have hd := (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.comp_hasDerivAt t
      ((hsol p hp).2 t ht).2
    change HasDerivAt (fun v => Φ (p, v)) (Z ((Ψ (p, t)).1, Φ (p, t))) t at hd
    rw [hstationary p hp t ht] at hd
    exact ⟨((hsol p hp).2 t ht).1.2, hd⟩
  · intro p hp t ht
    have htτ : t ∈ Ioo (-τ) τ := abs_lt.mp (ht.trans (by linarith))
    have hs := hnorm p hp t ht
    refine ⟨?_, ?_⟩
    · exact (norm_snd_le (Ψ (p, t) - p)).trans hs.1
    · intro n hn hnr
      have hg : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q : ℝ × (P × E) => Ψ (q.2, q.1)) (t, p) :=
        (hΨ.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hp, htτ⟩)).comp (t, p)
          (contDiff_snd.prodMk contDiff_fst).contDiffAt
      have hh := (ContinuousLinearMap.snd ℝ P E).norm_iteratedFDeriv_comp_left hg
        (n := n) (by simp)
      have hj : ‖iteratedFDeriv ℝ n (fun q : ℝ × (P × E) => Φ (q.2, q.1)) (t, p)‖ ≤
          2 * (1 + ε⁻¹) ^ n := hh.trans
        ((mul_le_mul (ContinuousLinearMap.norm_snd_le ℝ P E) (hs.2 n hn hnr)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
      refine ⟨hj, ?_⟩
      let L : (ℝ × (P × E)) →L[ℝ] E :=
        (ContinuousLinearMap.snd ℝ P E).comp (ContinuousLinearMap.snd ℝ ℝ (P × E))
      have hL : ‖L‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound L zero_le_one
        intro q
        change ‖q.2.2‖ ≤ 1 * ‖q‖
        simpa only [one_mul] using (norm_snd_le q.2).trans (norm_snd_le q)
      have hgf : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q : ℝ × (P × E) => Φ (q.2, q.1)) (t, p) :=
        hg.continuousLinearMap_comp (ContinuousLinearMap.snd ℝ P E)
      exact (norm_smooth_displacement_positive_jet_le hgf L n hn hj).trans
        (add_le_add_right hL _)

end RothschildStein.G1
