-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualJointTransportedKernel
public import RothschildStein.G4.JointAdjointJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The ACTUAL transported Taylor remainder is jointly smooth
in parameters, initial point and transported time on its actual open
reverse-endpoint overlap (BB Lemma 9.48, pp. 441–443). -/
theorem actual_parameterFlow_taylor_remainder_contDiffOn {P : Type*} {N : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [CompleteSpace P]
    {A : Set P} {Ω : Set (Fin N → ℝ)} {U : Set (P × (Fin N → ℝ))}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    (Z Y : P × (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (A ×ˢ Ω))
    {τ : ℝ} (hτ : 0 < τ) (Φ : (P × (Fin N → ℝ)) × ℝ → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (q : ℕ) :
    let S := (U ×ˢ Ioo (-τ) τ) ∩ {v | (v.1.1, Φ (v.1, -v.2)) ∈ U}
    IsOpen S ∧ ContDiffOn ℝ (⊤ : ℕ∞)
      (fun v => (fderiv ℝ (fun y => Φ ((v.1.1, y), v.2)) (Φ (v.1, -v.2)))
        (Y (v.1.1, Φ (v.1, -v.2))) -
          ∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j * v.2 ^ j / (j.factorial : ℝ)) •
            (((spatialBracketFamily Z)^[j] Y) v.1)) S := by
  intro S
  obtain ⟨hS, hP⟩ := actual_parameterFlow_transported_kernel_contDiffOn
    hA hΩ hU hUA hZ hτ Φ hc hΦ Y (hY.mono hUA)
  refine ⟨hS, hP.sub ?_⟩
  apply ContDiffOn.sum
  intro j _
  have hw : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : (P × (Fin N → ℝ)) × ℝ => (-1 : ℝ) ^ j * v.2 ^ j / (j.factorial : ℝ)) := by
    fun_prop
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞) ((spatialBracketFamily Z)^[j] Y) U :=
    (spatialBracketFamily_iterate_contDiffOn (hA.prod hΩ) hZ hY j).mono hUA
  exact hw.contDiffOn.smul (hJ.comp contDiffOn_fst (fun v hv => hv.1.1))

end RothschildStein.G4
