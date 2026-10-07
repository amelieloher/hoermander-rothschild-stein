-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualJointTransportedKernel
public import RothschildStein.G4.JointAdjointJets
public import RothschildStein.G4.BracketPolynomialIntegral

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- The ACTUAL integrated Taylor remainder agrees near the base
point with the transported coefficient integral minus its correctly
normalized signed bracket polynomial (BB Lemma 9.48, pp. 441–443). -/
theorem parameterFlow_integrated_taylor_remainder_eventuallyEq {P : Type*} {N : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (Z Y : P × (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω))
    {τ : ℝ} (hτ : 1 < τ) (Φ : (P × (Fin N → ℝ)) × ℝ → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    {p : P × (Fin N → ℝ)} (hp : p ∈ U)
    (hend : ∀ s ∈ Icc (0 : ℝ) 1, (p.1, Φ (p, -s)) ∈ U) (q : ℕ) :
    (fun v => ∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun y => Φ ((v.1, y), t)) (Φ (v, -t))) (Y (v.1, Φ (v, -t))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) v)) =ᶠ[𝓝 p]
    (fun v => (∫ t in (0 : ℝ)..1,
      (fderiv ℝ (fun y => Φ ((v.1, y), t)) (Φ (v, -t))) (Y (v.1, Φ (v, -t)))) -
        ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) v)) := by
  obtain ⟨hS, hK⟩ := actual_parameterFlow_transported_kernel_contDiffOn
    hA hΩ hU hUA hZ (show 0 < τ by linarith) Φ hc hΦ Y (hY.mono hUA)
  let S := (U ×ˢ Ioo (-τ) τ) ∩ {v | (v.1.1, Φ (v.1, -v.2)) ∈ U}
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, (p, s) ∈ S := fun s hs =>
    ⟨⟨hp, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩, hend s hs⟩
  have he : ∀ᶠ v in 𝓝 p, ∀ s ∈ Icc (0 : ℝ) 1, (v, s) ∈ S :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun s hs => hS.mem_nhds (hseg s hs))
  filter_upwards [he] with v hv
  have hInt : IntervalIntegrable
      (fun t => (fderiv ℝ (fun y => Φ ((v.1, y), t)) (Φ (v, -t)))
        (Y (v.1, Φ (v, -t)))) volume 0 1 :=
    (hK.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hv).intervalIntegrable_of_Icc zero_le_one
  have hPoly : IntervalIntegrable
      (fun t : ℝ => ∑ j ∈ Finset.range (q + 1),
        ((-1 : ℝ) ^ j * t ^ j / (j.factorial : ℝ)) •
          (((spatialBracketFamily Z)^[j] Y) v)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro j _
    exact (((continuous_const.mul (continuous_id.pow j)).div_const _).smul continuous_const)
  rw [intervalIntegral.integral_sub hInt hPoly, integral_signed_bracket_polynomial]

end RothschildStein.G4
