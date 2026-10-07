-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalPowerEndpointZeroSlice

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.G1

/-- Actual positive and negative retained-log endpoint models
have smooth time-power factors with opposite leading values throughout
their common local base-point domain (BB Lemma 1.52, pp. 30–31). -/
theorem exists_local_opposite_endpoint_model_factors {m n : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin n → ℝ))} (hU : IsOpen U)
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hzero : ∀ x, (0, x) ∈ U → F (0, x) = x)
    (H : ℝ → (Fin m → ℝ)) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (k : ℕ) (hk : 0 < k) (x₀ : Fin n → ℝ) (hx₀ : (0, x₀) ∈ U) :
    ∃ V : Set (ℝ × (Fin n → ℝ)), IsOpen V ∧ (0, x₀) ∈ V ∧
      ∃ Rp Rm : (ℝ × (Fin n → ℝ)) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Rp V ∧ ContDiffOn ℝ (⊤ : ℕ∞) Rm V ∧
        (∀ q ∈ V, F (q.1 ^ k • H q.1, q.2) - q.2 = q.1 ^ k • Rp q ∧
          F (-(q.1 ^ k • H q.1), q.2) - q.2 = q.1 ^ k • Rm q) ∧
        (∀ x, (0, x) ∈ V →
          Rp (0, x) = fderiv ℝ (fun z => F (z, x)) 0 (H 0) ∧
          -Rm (0, x) = Rp (0, x)) := by
  obtain ⟨Vp, hVp, hVp₀, Rp, hRp, hep, hRp₀⟩ :=
    exists_local_power_endpoint_factor_with_zero_slice hU F hF hzero H hH k hk x₀ hx₀
  obtain ⟨Vm, hVm, hVm₀, Rm, hRm, hem, hRm₀⟩ :=
    exists_local_power_endpoint_factor_with_zero_slice hU F hF hzero (fun t => -H t)
      hH.neg k hk x₀ hx₀
  refine ⟨Vp ∩ Vm, hVp.inter hVm, ⟨hVp₀, hVm₀⟩, Rp, Rm,
    hRp.mono inter_subset_left, hRm.mono inter_subset_right, ?_, ?_⟩
  · intro q hq
    refine ⟨hep q hq.1, ?_⟩
    simpa only [smul_neg] using hem q hq.2
  · intro x hx
    refine ⟨hRp₀ x hx.1, ?_⟩
    rw [hRm₀ x hx.2, hRp₀ x hx.1, map_neg, neg_neg]

end RothschildStein.G1
