-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.RadialFactorZeroSlice

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G1

/-- Substitution of a smooth coefficient polynomial into the
actual radial endpoint factor preserves its leading coefficient.
This is the time-power factor used for a retained commutator logarithm. -/
theorem exists_local_power_endpoint_factor_with_zero_slice {m n : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin n → ℝ))} (hU : IsOpen U)
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hzero : ∀ x, (0, x) ∈ U → F (0, x) = x)
    (H : ℝ → (Fin m → ℝ)) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (k : ℕ) (hk : 0 < k) (x₀ : Fin n → ℝ) (hx₀ : (0, x₀) ∈ U) :
    ∃ V : Set (ℝ × (Fin n → ℝ)), IsOpen V ∧ (0, x₀) ∈ V ∧
      ∃ R : (ℝ × (Fin n → ℝ)) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) R V ∧
        (∀ q ∈ V, F (q.1 ^ k • H q.1, q.2) - q.2 = q.1 ^ k • R q) ∧
        (∀ x, (0, x) ∈ V → R (0, x) = fderiv ℝ (fun z => F (z, x)) 0 (H 0)) := by
  obtain ⟨W, hW, hW₀, G, hG, he, _hg₀⟩ :=
    exists_local_radial_endpoint_factor hU F hF hzero (H 0) x₀ hx₀
  let A : (ℝ × (Fin n → ℝ)) → ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
    fun q => (fun _ => q.1 ^ k, (H q.1, q.2))
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    (contDiff_pi.mpr (fun _ => contDiff_fst.pow k)).prodMk
      ((hH.comp contDiff_fst).prodMk contDiff_snd)
  have hA₀ : A (0, x₀) = (0, (H 0, x₀)) := by
    simp only [A, zero_pow hk.ne']
    rfl
  let B : ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) →
      ((Fin m → ℝ) × (Fin n → ℝ)) := fun q => (q.1 0 • q.2.1, q.2.2)
  have hB : ContDiff ℝ (⊤ : ℕ∞) B :=
    (((contDiff_apply ℝ ℝ 0).comp contDiff_fst).smul contDiff_snd.fst).prodMk contDiff_snd.snd
  let W' := W ∩ B ⁻¹' U
  have hW' : IsOpen W' := hW.inter (hU.preimage hB.continuous)
  have hW'₀ : A (0, x₀) ∈ W' := by
    refine ⟨by simpa only [hA₀] using hW₀, ?_⟩
    simpa only [mem_preimage, hA₀, B, Pi.zero_apply, zero_smul] using hx₀
  refine ⟨A ⁻¹' W', hW'.preimage hA.continuous, hW'₀, G ∘ A,
    hG.comp hA.contDiffOn (fun _ hq => hq.1), ?_, ?_⟩
  · intro q hq
    exact he (A q) hq.1
  · intro x hx
    have hAx : A (0, x) = (0, (H 0, x)) := by
      simp only [A, zero_pow hk.ne']
      rfl
    have hxU : (0, x) ∈ U := by
      simpa only [W', mem_inter_iff, mem_preimage, hAx, B, Pi.zero_apply, zero_smul] using hx.2
    have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Fin m → ℝ => (z, x)) 0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have hf : DifferentiableAt ℝ (fun z : Fin m → ℝ => F (z, x)) 0 :=
      ((hF.contDiffAt (hU.mem_nhds hxU)).comp (f := fun z : Fin m → ℝ => (z, x))
        (0 : Fin m → ℝ) hi).differentiableAt (by simp)
    have hxW : (0, (H 0, x)) ∈ W := by simpa only [hAx] using hx.1
    simpa only [Function.comp_apply, hAx] using
      local_radial_factor_zero_value F hW G hG he (H 0) x hxW hf

end RothschildStein.G1
