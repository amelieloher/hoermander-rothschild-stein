-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.QuadraticTest
public import RothschildStein.H1.EliminateAtom

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The complete residual-atom identity forces the atom to
vanish for the standing operator, using an actual compact quadratic test
(BB (6.6)–(6.8), pp. 251–253). -/
theorem StandingHypotheses.eliminate_residualAtom
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (hΩ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ Ω, G.dilate t x ∈ Ω)
    {γ : (Fin N → ℝ) → ℝ} (hγ : Integrable γ) {α : ℝ}
    (hidentity : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields φ x) +
        α * sumSquaresWithDriftTranspose H.fields φ 0 = φ 0) :
    α = 0 ∧ ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 := by
  obtain ⟨φ, hz, hop⟩ := H.exists_quadraticTest G Ω h0
  have he : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDrift (H.reverseDrift G).fields ψ x) +
        α * sumSquaresWithDrift (H.reverseDrift G).fields ψ 0 = ψ 0 := by
    intro ψ
    simpa only [H.reverseDrift_operator G ψ ψ.contDiff] using hidentity ψ
  have hp : sumSquaresWithDrift (H.reverseDrift G).fields φ 0 ≠ 0 := by
    rw [H.reverseDrift_operator G φ φ.contDiff]
    exact hop
  have hα := residual_atom_eq_zero G Ω hΩ (H.reverseDrift G).fields
    (fun i => ((H.reverseDrift G).fields_smooth G i).contDiffOn)
    ((H.reverseDrift G).operator_homogeneous G) hγ he φ hz hp
  refine ⟨hα, ?_⟩
  intro ψ
  simpa only [hα, zero_mul, add_zero] using hidentity ψ

end RothschildStein.H1
