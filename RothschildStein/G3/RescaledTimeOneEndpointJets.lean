-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ShortFlowEndpointJets
public import RothschildStein.G3.CoefficientRescalingMap
public import RothschildStein.G3.ExponentialFlowMaps
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

/-- Uniform short-time mixed jets yield explicit time-one coefficient
endpoint jets after reciprocal coefficient/time rescaling (BB pp. 413–415). -/
theorem norm_rescaled_timeOne_endpoint_jet_le {m N : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin N → ℝ))} (hU : IsOpen U) {τ ε : ℝ}
    (hε : 0 < ε) (hετ : 4*ε < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    {q : (Fin m → ℝ) × (Fin N → ℝ)}
    (hq : coefficientRescalingMap (ε/4) q ∈ U)
    {Q n : ℕ} (hn : 1 ≤ n) (hnQ : n ≤ Q)
    (hjet : ∀ z ∈ U, ∀ t, |t| < ε → ∀ j, 1 ≤ j → j ≤ Q →
      ‖iteratedFDeriv ℝ j (fun z : ℝ × ((Fin m → ℝ) × (Fin N → ℝ)) =>
        Φ (z.2,z.1)) (t,z)‖ ≤ 2*(1+ε⁻¹)^j) :
    ‖iteratedFDeriv ℝ n (finiteLieTimeOneMap (Φ ∘ G4.flowScale (ε/4))) q‖ ≤
      n.factorial * (2*(1+ε⁻¹)^Q) * (1+|(ε/4)⁻¹|)^n := by
  have ht : |ε/4| < ε := by rw [abs_of_pos (by positivity : 0 < ε/4)]; linarith
  have htτ : ε/4 ∈ Ioo (-τ) τ := by constructor <;> linarith
  have he := norm_shortFlow_endpoint_linear_reparametrized_jet_le hU hε ht htτ
    (by linarith [abs_nonneg (ε/4)⁻¹] : 1 ≤ 1+|(ε/4)⁻¹|) Φ hΦ
    (coefficientRescalingMap (ε/4)) (norm_coefficientRescalingMap_le (ε/4)) hq hn hnQ hjet
  have hfun : finiteLieTimeOneMap (Φ ∘ G4.flowScale (ε/4)) =
      (fun y => Φ (coefficientRescalingMap (ε/4) y,ε/4)) := by
    funext y
    simp [finiteLieTimeOneMap, G4.flowScale,
      coefficientRescalingMap_apply]
  rw [hfun]
  exact he
end RothschildStein.G3
