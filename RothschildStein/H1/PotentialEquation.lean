-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PotentialFubini
public import RothschildStein.H1.OperatorPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The globally smooth group potential solves the standing
operator pointwise. Fubini is justified by the common compact-support
estimate, and the translated fundamental identity gives the weak equation
(BB Theorem 6.20(3), printed pp. 270–271). -/
theorem StandingHypotheses.fundamentalPotential_equation
    (H : StandingHypotheses G q) {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hfund : ∀ ψ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ y, Γ y * sumSquaresWithDriftTranspose H.fields ψ y) = ψ 0)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcφ : HasCompactSupport φ) :
    sumSquaresWithDrift H.fields (fun x => ∫ y, Γ (G.mul (G.inv y) x) * φ y) = φ := by
  apply H.operator_eq_of_weak_pairing G (contDiff_fundamentalPotential G hΓ hφ hcφ) hφ.continuous
  intro ψ hψ hcψ
  let ψt : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨ψ, hψ, hcψ, subset_univ _⟩
  let η := sumSquaresWithDriftTransposeTest ⊤ H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) ψt
  have he : (η : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields ψ :=
    funext (H.transposeTest_apply G ⊤ ψt)
  rw [fundamentalPotential_pairing G hΓ hφ.continuous hcφ
    (he ▸ η.contDiff.continuous) (he ▸ η.hasCompactSupport)]
  congr 1
  funext y
  rw [H.fundamental_representation G Γ hfund ψ hψ hcψ y]

end RothschildStein.H1
