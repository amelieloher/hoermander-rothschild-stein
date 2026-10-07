-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftTransposeTest
public import RothschildStein.S.TestPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- The equations of smooth convolution approximants pass to
the actual local Lp limit, in the fixed drift transpose pairing
(BB p. 374). No equation for the limit is assumed. -/
theorem equation_of_lp_pairing_limits {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f v : ℕ → (Fin n → ℝ) → ℝ) (F u : (Fin n → ℝ) → ℝ)
    (hf : ∀ j, MemLp (f j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hv : ∀ j, MemLp (v j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hF : MemLp F p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hft : Tendsto (fun j => eLpNorm (f j - F) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0))
    (hut : Tendsto (fun j => eLpNorm (v j - u) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0))
    (heq : ∀ j (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)),
      (∫ x in (Ω : Set (Fin n → ℝ)), f j x * ψ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), v j x * sumSquaresWithDriftTranspose X ψ x) :
    ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x in (Ω : Set (Fin n → ℝ)), F x * ψ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), u x * sumSquaresWithDriftTranspose X ψ x := by
  intro ψ
  have hleft := S.tendsto_testIntegral_of_tendsto_eLpNorm Ω p r ψ f F hf hF hft
  have hright := S.tendsto_testIntegral_of_tendsto_eLpNorm Ω p r
    (driftTransposeTest Ω X hX ψ) v u hv hu hut
  simp only [driftTransposeTest_apply] at hright
  exact tendsto_nhds_unique hleft (hright.congr (fun j => (heq j ψ).symm))

end RothschildStein.H3
