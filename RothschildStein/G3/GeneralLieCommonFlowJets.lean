-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieStateCompositionJets
@[expose] public section
noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.G3

/-- Every retained Lie-input pair has the required weighted radial jets on
one actual common family. The family is shared across all pairs. -/
theorem generalLie_joint_BCH_jets_of_common_flow {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ ε B : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hB : 0 ≤ B)
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),t) ∈ Ω ∧
          HasDerivAt (fun v => Φ ((D.basis.equivFun z,x),v))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),t))) t)
    (hjets : ∀ x ∈ Ω, ∀ i k, k ≤ 3*s+2 → ‖iteratedFDeriv ℝ k (X i) x‖ ≤ B)
    (f g : formalSpan a s p) (hs : 1 ≤ s) {x : Fin N → ℝ} (hx : x ∈ Ω₀)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x ε) ×ˢ Ioo (-2) 2))
    (hzero : finiteLieTimeOneMap Φ (0,x) = x) :
    ∀ k ≤ s,
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieSuccessivePointMap D Φ f g q.1 (x+q.2)) 0 =
      iteratedFDeriv ℝ k (fun q : ℝ × (Fin N → ℝ) =>
        generalLieBCHPointMap D Φ f g q.1 (x+q.2)) 0 := by
  have hj := generalLie_shifted_pointMaps_contDiffAt D f g hε Φ hΦ hzero
  apply frechet_jets_eq_of_radial_power_error (hj.1.of_le (by simp)) (hj.2.of_le (by simp))
  intro v
  let E := generalLieBCHErrorCoefficient D f g (primitiveWordJetBudget D (3*s+2) B)
    (max (generalLieTravelBudget D f B+generalLieTravelBudget D g B+
      generalLieTravelBudget D (modelProduct f g) B) 1)
  refine ⟨E*|v.1|^(s+1),?_⟩
  have ht : Tendsto (fun t : ℝ => t*v.1) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun t : ℝ => t*v.1) by fun_prop).tendsto 0
  have hQ : Tendsto (fun t : ℝ => (t*v.1,x+t • v.2)) (𝓝 0) (𝓝 (0,x)) := by
    simpa using (show Continuous (fun t : ℝ => (t*v.1,x+t • v.2)) by fun_prop).tendsto 0
  have hy : ∀ᶠ t : ℝ in 𝓝 0, x+t • v.2 ∈ Ω₀ :=
    (continuous_snd.tendsto (0,x) |>.comp hQ).eventually (Ω₀.isOpen.mem_nhds hx)
  have hfirst : ∀ᶠ t : ℝ in 𝓝 0,
      finiteLieTimeOneMap Φ (dilatedInputCoordinates D f (t*v.1),x+t • v.2) ∈ Ω₀ := by
    have hh := (generalLieSinglePointMap_contDiffAt D f hε Φ hΦ).continuousAt.tendsto.comp hQ
    have hh' : Tendsto (fun t : ℝ => finiteLieTimeOneMap Φ
        (dilatedInputCoordinates D f (t*v.1),x+t • v.2)) (𝓝 0) (𝓝 x) := by
      simpa only [Function.comp_def,dilatedInputCoordinates_zero,hzero] using hh
    exact hh'.eventually (Ω₀.isOpen.mem_nhds hx)
  have hc : ∀ z : formalSpan a s p, ∀ᶠ t : ℝ in 𝓝 0,
      dilatedInputCoordinates D z (t*v.1) ∈ ball 0 σ := by
    intro z
    have hh := (dilatedInputCoordinates_contDiff D z).continuous.tendsto 0 |>.comp ht
    have hh' : Tendsto (fun t : ℝ => dilatedInputCoordinates D z (t*v.1)) (𝓝 0) (𝓝 0) := by
      simpa only [Function.comp_def,dilatedInputCoordinates_zero] using hh
    exact hh'.eventually (isOpen_ball.mem_nhds (by simpa using hσ))
  have hd : ∀ᶠ t : ℝ in 𝓝 0, |t*v.1| ≤ 1 := by
    have hh := ht.norm.eventually (eventually_lt_nhds (by simp : ‖(0 : ℝ)‖ < 1))
    filter_upwards [hh] with t ht
    exact (by simpa only [Real.norm_eq_abs] using ht.le)
  filter_upwards [hy,hfirst,hc f,hc g,hc (modelProduct f g),hd] with t hy hf hc₁ hc₂ hc₃ hd
  have he := generalLiePointMaps_error_of_common_flow D Ω Ω₀ X hX Φ hODE f g (t*v.1)
    hs hB hd hjets hc₁ hc₂ hc₃ hy hf
  change ‖generalLieSuccessivePointMap D Φ f g (t*v.1) (x+t • v.2)-
    generalLieBCHPointMap D Φ f g (t*v.1) (x+t • v.2)‖ ≤ |t*v.1|^(s+1)*E at he
  simpa only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_mul,mul_pow,
    mul_assoc,mul_comm,mul_left_comm] using he
end RothschildStein.G3
