-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ResidualOrderZeroAtom
public import RothschildStein.H1.StandingAtomElimination
public import RothschildStein.H1.FundamentalDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The full order-zero fundamental identity and integrable
representation off zero imply representation on every test and the local
fundamental function identity. The missing distribution regularity step
is not part of this post-representation theorem (BB pp. 251–253, 263–264). -/
theorem StandingHypotheses.localFundamental_from_orderZeroRepresentation
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (hΩ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ Ω, G.dilate t x ∈ Ω)
    (T : TestFunction Ω ℝ (⊤ : ℕ∞) →ₗ[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ, |T φ| ≤ C * ‖(TestFunction.toBoundedContinuousFunctionCLM ℝ) φ‖)
    (hfund : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      T (sumSquaresWithDriftTransposeTest Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ) = φ 0)
    {γ : (Fin N → ℝ) → ℝ} (hγ : Integrable γ)
    (hrep : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (0 : Fin N → ℝ) ∉ tsupport (φ : (Fin N → ℝ) → ℝ) → T φ = ∫ x, γ x * φ x) :
    (∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞), T φ = ∫ x, γ x * φ x) ∧
      (∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
        (∫ x, γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0) := by
  obtain ⟨α, he⟩ := orderZero_representation_residual_atom Ω h0 T hC hbound hγ hrep
  have hidentity : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields φ x) +
        α * sumSquaresWithDriftTranspose H.fields φ 0 = φ 0 := by
    intro φ
    let ψ := sumSquaresWithDriftTransposeTest Ω H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φ
    have hψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
      funext (H.transposeTest_apply G Ω φ)
    have hh := he ψ
    rw [hfund φ] at hh
    change φ 0 = (∫ x, γ x * ψ x) + α * ψ 0 at hh
    rw [hψ] at hh
    exact hh.symm
  obtain ⟨hα, hlocal⟩ := H.eliminate_residualAtom G Ω h0 hΩ hγ hidentity
  refine ⟨?_, hlocal⟩
  intro φ
  simpa only [hα, zero_mul, add_zero] using he φ

end RothschildStein.H1
