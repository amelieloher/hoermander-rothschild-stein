-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.LocalizedForcing
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.Distribution

/-- Bundle the adjoint `hormanderAdjointTest` on actual
real tests, retaining all drift and zeroth-order terms. -/
def adjointTest {k N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) : TestFunction Ω ℝ (⊤ : ℕ∞) :=
  ⟨Hormander.Interface.hormanderAdjointTest X c ψ,
    Hormander.F.hormanderAdjointTest_smooth Ω.isOpen X hX c hc ψ ψ.contDiff ψ.tsupport_subset,
    ψ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
      (Hormander.F.hormanderAdjointTest_tsupport_subset X c ψ),
    (Hormander.F.hormanderAdjointTest_tsupport_subset X c ψ).trans ψ.tsupport_subset⟩

/-- The bundled adjoint is the literal `hormanderAdjointTest`
formula, without a choice of coefficient extension. -/
theorem adjointTest_apply {k N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    adjointTest Ω X c hX hc ψ x = Hormander.Interface.hormanderAdjointTest X c ψ x := rfl

end RothschildStein.Distribution
