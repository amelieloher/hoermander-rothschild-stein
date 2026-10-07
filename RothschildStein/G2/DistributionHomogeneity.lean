-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.TransposeHomogeneity
public import RothschildStein.Definitions.HomogeneousGroup.HasHomogeneousDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory TopologicalSpace
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Pullback of a test function by a positive coordinate dilation
(BB Definition 3.76, p. 143). -/
def dilatedTest (t : ℝ) (ht : 0 < t)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
  ⟨φ ∘ G.dilate t, φ.contDiff.comp (contDiff_dilate G t),
    φ.hasCompactSupport.comp_homeomorph (dilationHomeomorph G t ht), Set.subset_univ _⟩

/-- The test-function pullback has exactly the dilation action. -/
theorem dilatedTest_apply (t : ℝ) (ht : 0 < t)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    dilatedTest G t ht φ x = φ (G.dilate t x) := rfl

/-- The existential predicate is equivalent to the concrete pullback formula
(BB Definition 3.76, p. 143). -/
theorem hasHomogeneousDistribution_iff (α : ℝ)
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    G.HasHomogeneousDistribution α T ↔ ∀ t (ht : 0 < t) φ,
      T (dilatedTest G t ht φ) = t ^ (-(G.homogeneousDimension : ℝ) - α) * T φ := by
  constructor
  · intro h t ht φ
    obtain ⟨ψ, hψ, hs⟩ := h t ht φ
    have he : ψ = dilatedTest G t ht φ := by ext x; exact hψ x
    rwa [he] at hs
  · intro h t ht φ
    exact ⟨dilatedTest G t ht φ, fun _ => rfl, h t ht φ⟩

end RothschildStein.G2
