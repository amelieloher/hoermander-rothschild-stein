-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.AdjointTest
public import Hormander.F.Coordinates
public import Hormander.F.DifferentialTransport
public import Hormander.F.SchwartzTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.Distribution

/-- pull a Euclidean cutoff to an actual real test
on the original coordinate carrier, using the existing homeomorphism. -/
def pullEuclideanCutoff {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (φ : Hormander.F.E₂ N → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ Hormander.F.coordinateEquiv N '' (Ω : Set (Fin N → ℝ))) :
    TestFunction Ω ℝ (⊤ : ℕ∞) := by
  refine ⟨fun x => φ (Hormander.F.coordinateEquiv N x),
    hφ.comp (Hormander.F.coordinateEquiv N).contDiff,
    hc.comp_isClosedEmbedding (Hormander.F.coordinateEquiv N).toHomeomorph.isClosedEmbedding, ?_⟩
  change tsupport (φ ∘ (Hormander.F.coordinateEquiv N).toHomeomorph) ⊆ (Ω : Set (Fin N → ℝ))
  rw [tsupport_comp_eq_preimage φ (Hormander.F.coordinateEquiv N).toHomeomorph]
  intro x hx
  obtain ⟨y, hy, he⟩ := hΩ hx
  have hexy : y = x := (Hormander.F.coordinateEquiv N).injective he
  simpa only [hexy] using hy

/-- exact support transport for the pulled cutoff,
used to retain the nested plateau conditions. -/
theorem tsupport_pullEuclideanCutoff {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (φ : Hormander.F.E₂ N → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ)
    (hΩ : tsupport φ ⊆ Hormander.F.coordinateEquiv N '' (Ω : Set (Fin N → ℝ))) :
    tsupport (pullEuclideanCutoff Ω φ hφ hc hΩ) =
      (Hormander.F.coordinateEquiv N) ⁻¹' tsupport φ := by
  change tsupport (φ ∘ (Hormander.F.coordinateEquiv N).toHomeomorph) = _
  exact tsupport_comp_eq_preimage φ (Hormander.F.coordinateEquiv N).toHomeomorph

end RothschildStein.Distribution
