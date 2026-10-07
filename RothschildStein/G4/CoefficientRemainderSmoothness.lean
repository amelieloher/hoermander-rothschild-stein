-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.PartialParameterJets
public import RothschildStein.G4.ParameterFlowSmoothness
public import RothschildStein.G4.JointAdjointJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual original-coefficient derivative minus its signed
endpoint adjoint polynomial is jointly smooth on the original local-flow
domain (BB Lemma 9.48, pp. 441–443). -/
theorem linear_field_flow_coefficient_remainder_contDiffOn {m N : ℕ}
    {A : Set (Fin m → ℝ)} {Ω U : Set (Fin N → ℝ)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (W : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hW : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (W j) Ω)
    {τ : ℝ} (hτ : 1 < τ)
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ ((A ×ˢ U) ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ A ×ˢ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (∑ j, p.1 j • W j (Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (i : Fin m) (q : ℕ) :
    let Z : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => ∑ j, p.1 j • W j p.2
    let Y : ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun p => W i p.2
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p =>
      fderiv ℝ (fun a => Φ ((a, p.2), 1)) p.1 (Pi.single i 1) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) (p.1, Φ (p, 1)))) (A ×ˢ U) := by
  intro Z Y
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω) := by
    apply ContDiffOn.sum
    intro j hj
    exact (((contDiff_apply ℝ ℝ j).comp contDiff_fst).contDiffOn).smul
      ((hW j).comp contDiffOn_snd (fun p hp => hp.2))
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω) :=
    (hW i).comp contDiffOn_snd (fun p hp => hp.2)
  have ht₁ : (1 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => Φ (p, 1)) (A ×ˢ U) :=
    (parameterFlow_contDiffOn hA hΩ (hA.prod hU) (prod_mono Subset.rfl hUΩ)
      hZ (show 0 < τ by linarith) Φ hc hΦ).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun p hp => ⟨hp, ht₁⟩)
  apply ((partial_parameter_fderiv_contDiffOn (hA.prod hU) hF).clm_apply contDiffOn_const).sub
  apply ContDiffOn.sum
  intro j hj
  have hJ := spatialBracketFamily_iterate_contDiffOn (hA.prod hΩ) hZ hY j
  have hh := hJ.comp (contDiffOn_fst.prodMk hF)
    (fun p hp => ⟨hp.1, ((hΦ p hp).2 1 ht₁).2⟩)
  exact hh.const_smul ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ))

end RothschildStein.G4
