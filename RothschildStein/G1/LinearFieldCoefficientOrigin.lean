-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CoefficientEndpointIntegral
public import RothschildStein.G4.ZeroCoefficientFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- At zero coefficients, the genuine time-one flow's coefficient
columns are exactly its vector fields. The endpoint integral reduces to
an identity flow, without any independent Jacobian assumption
(BB Lemma 9.48, pp. 441–442; Theorem 1.48, pp. 32–34). -/
theorem linear_field_timeOne_coefficient_origin {m n : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin n → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    (hz : (0 : Fin m → ℝ) ∈ A) {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (p, v))
        (∑ j, p.1 j • W j (Φ (p, t))) t ∧ Φ (p, t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) (i : Fin m) :
    fderiv ℝ (fun z => Φ ((z, x), 1)) 0 (Pi.single i 1) = W i x := by
  have hτpos : 0 < τ := zero_lt_one.trans hτ
  have hzero (y : Fin n → ℝ) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Ioo (-τ) τ) :
      Φ ((0, y), t) = y :=
    G4.linear_field_flow_zero_coefficients W hτpos Φ hΦ hz hy ht
  have ht1 : (1 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hfwd : ∀ t ∈ Icc (0 : ℝ) 1, Φ ((0, x), t) ∈ U := by
    intro t ht
    rw [hzero x hx t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    exact hx
  rw [G4.linear_field_flow_coefficient_endpoint_integral hA hΩ hU hUΩ W hW hτ
    Φ hc hΦ hz hx hfwd i]
  calc
    _ = ∫ t in (0 : ℝ)..1, W i x := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      have htp : t ∈ Ioo (-τ) τ := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      have htn : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht'.1, ht'.2], by linarith [ht'.1]⟩
      dsimp only
      rw [hzero x hx 1 ht1, hzero x hx (-t) htn]
      have he : (fun y => Φ ((0, y), t)) =ᶠ[𝓝 x] (fun y => y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact hzero y hy t htp
      rw [he.fderiv_eq]
      change (fderiv ℝ (id : (Fin n → ℝ) → (Fin n → ℝ)) x) (W i x) = W i x
      rw [fderiv_id]
      rfl
    _ = W i x := by simp

end RothschildStein.G1
