-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.FramePatchRepresentative
public import RothschildStein.Distribution.SmoothDistributionGluing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- distributional Hörmander hypoellipticity in positive
dimension, with real smooth fields, drift and a zeroth-order term.
The input is a complex-valued distribution on real test functions. The
output is a smooth complex-valued function on the original open set whose distribution
agrees with the input on every compactly supported test function. -/
theorem exists_smooth_representative_of_distribution_equation {k N : ℕ} (hN : 0 < N)
    (Ω : Opens (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hspan : Hormander.Interface.LieAlgebraSpansOn (Ω : Set (Fin N → ℝ)) X)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω X c hX hc ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ) :
    ∃ F : (Fin N → ℝ) → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F (Ω : Set (Fin N → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x • F x := by
  classical
  have hlocal (x : Ω) : ∃ W : Set (Fin N → ℝ), IsOpen W ∧ (x : Fin N → ℝ) ∈ W ∧ W ⊆ Ω ∧
      ∃ F : (Fin N → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ W → T ψ = ∫ y, ψ y • F y := by
    obtain ⟨P⟩ := Hormander.F.exists_local_frame_patch hN Ω.isOpen X c x x.property hX hspan hc
    exact exists_local_distribution_representative_on_framePatch hN Ω X c hX hc T g hg heq x P
  choose U hU hxU hUΩ F hF hrep using hlocal
  have hcover : ∀ x ∈ (Ω : Set (Fin N → ℝ)), ∃ i : Ω, x ∈ U i := by
    intro x hx
    exact ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  exact exists_smooth_distribution_gluing Ω T U F hU hUΩ hcover (fun i => (hF i).contDiffOn) hrep

end RothschildStein.Distribution
