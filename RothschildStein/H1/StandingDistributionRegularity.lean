-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.RealHypoellipticity
public import RothschildStein.H1.WeakRegularity
public import RothschildStein.H1.FundamentalDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The standing group's actual distributional regularity
interface, using its transpose-test operator. This supplies
arbitrary-distribution regularity rather than a function-input premise. -/
theorem StandingHypotheses.exists_smooth_distributionRepresentative
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      T (sumSquaresWithDriftTransposeTest Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin N → ℝ)) ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * f x := by
  apply RothschildStein.Distribution.exists_real_smooth_representative_of_distribution_equation
    G.dimension_pos Ω H.fields 0 (fun i => (H.fields_smooth G i).contDiffOn)
    (H.spansOn G (Ω : Set (Fin N → ℝ))) contDiffOn_const T g hg
  intro ψ
  have ht : RothschildStein.Distribution.adjointTest Ω H.fields 0
      (fun i => (H.fields_smooth G i).contDiffOn) contDiffOn_const ψ =
      sumSquaresWithDriftTransposeTest Ω H.fields (fun i => (H.fields_smooth G i).contDiffOn) ψ := by
    ext x
    rw [RothschildStein.Distribution.adjointTest_apply,
      H.hormanderAdjointTest_eq_transpose G ψ ψ.contDiff, H.transposeTest_apply G]
  rw [ht]
  exact heq ψ

end RothschildStein.H1
